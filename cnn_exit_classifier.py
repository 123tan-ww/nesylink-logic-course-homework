from pathlib import Path

import numpy as np
import torch
from torch import nn

from Dataclass import ROOM_H, ROOM_W, TILE


EXIT_CLASSES = (
    "none",
    "normal",
    "locked_key_closed",
    "locked_key_open",
    "conditional",
)

EXIT_INFO = {
    "normal": ("normal", False),
    "locked_key_closed": ("locked_key", False),
    "locked_key_open": ("locked_key", True),
    "conditional": ("conditional", False),
}

EXIT_TILES_BY_DIR = {
    "north": [(4, 0), (5, 0)],
    "south": [(4, ROOM_H - 1), (5, ROOM_H - 1)],
    "west": [(0, 3), (0, 4)],
    "east": [(ROOM_W - 1, 3), (ROOM_W - 1, 4)],
}

EXIT_REGIONS = (
    ("north", (0, 4 * TILE, TILE, 6 * TILE)),
    ("south", (7 * TILE, 4 * TILE, 8 * TILE, 6 * TILE)),
    ("west", (3 * TILE, 0, 5 * TILE, TILE)),
    ("east", (3 * TILE, 9 * TILE, 5 * TILE, 10 * TILE)),
)


class ExitRegionCNN(nn.Module):
    def __init__(self, num_classes: int):
        super().__init__()
        self.features = nn.Sequential(
            nn.Conv2d(4, 24, 3, padding=1),
            nn.BatchNorm2d(24),
            nn.ReLU(inplace=True),
            nn.Conv2d(24, 24, 3, padding=1),
            nn.BatchNorm2d(24),
            nn.ReLU(inplace=True),
            nn.MaxPool2d(2),
            nn.Conv2d(24, 48, 3, padding=1),
            nn.BatchNorm2d(48),
            nn.ReLU(inplace=True),
            nn.Conv2d(48, 48, 3, padding=1),
            nn.BatchNorm2d(48),
            nn.ReLU(inplace=True),
            nn.MaxPool2d(2),
            nn.Conv2d(48, 96, 3, padding=1),
            nn.BatchNorm2d(96),
            nn.ReLU(inplace=True),
            nn.AdaptiveAvgPool2d((1, 1)),
        )
        self.classifier = nn.Sequential(
            nn.Dropout(0.15),
            nn.Linear(96, num_classes),
        )

    def forward(self, x):
        x = self.features(x).flatten(1)
        return self.classifier(x)


def pad_exit_patch(patch: np.ndarray) -> np.ndarray:
    patch = np.asarray(patch)
    if patch.ndim != 3 or patch.shape[2] != 3:
        raise ValueError(f"Expected HxWx3 patch, got {patch.shape}")
    h, w = patch.shape[:2]
    if (h, w) == (32, 32):
        return patch.astype(np.uint8, copy=False)
    if (h, w) not in {(16, 32), (32, 16)}:
        raise ValueError(f"Expected 16x32 or 32x16 exit patch, got {patch.shape}")
    result = np.zeros((32, 32, 3), dtype=np.uint8)
    y0 = (32 - h) // 2
    x0 = (32 - w) // 2
    result[y0:y0 + h, x0:x0 + w, :] = patch.astype(np.uint8, copy=False)
    return result


def exit_patches_to_tensor(patches) -> torch.Tensor:
    array = np.stack([pad_exit_patch(patch) for patch in patches], axis=0)
    array = array.astype(np.float32) / 255.0
    array = np.clip(array, 0.0, 1.0)

    rgb = (array - 0.5) / 0.5
    gray = (
        0.299 * array[:, :, :, 0]
        + 0.587 * array[:, :, :, 1]
        + 0.114 * array[:, :, :, 2]
    ).astype(np.float32)

    gx = np.zeros_like(gray)
    gy = np.zeros_like(gray)
    gx[:, :, 1:-1] = gray[:, :, 2:] - gray[:, :, :-2]
    gy[:, 1:-1, :] = gray[:, 2:, :] - gray[:, :-2, :]
    edge = np.sqrt(gx * gx + gy * gy)
    edge_max = edge.reshape(edge.shape[0], -1).max(axis=1)
    edge = edge / (edge_max[:, None, None] + 1e-6)

    features = np.concatenate(
        [rgb.transpose(0, 3, 1, 2), edge[:, None, :, :]],
        axis=1,
    )
    return torch.from_numpy(features.astype(np.float32))


class ExitRegionClassifier:
    def __init__(self, model_path=None, device="auto"):
        if model_path is None:
            model_path = (
                Path(__file__).resolve().parent
                / "weights"
                / "exit_region_cnn.pt"
            )

        self.model_path = Path(model_path).resolve()
        if not self.model_path.exists():
            raise FileNotFoundError(f"Checkpoint not found: {self.model_path}")

        if device == "auto":
            device = "cuda" if torch.cuda.is_available() else "cpu"
        self.device = torch.device(device)

        checkpoint = torch.load(
            self.model_path,
            map_location="cpu",
            weights_only=True,
        )
        self.classes = list(checkpoint["classes"])
        self.model = ExitRegionCNN(len(self.classes))
        self.model.load_state_dict(checkpoint["model_state_dict"])
        self.model.to(self.device)
        self.model.eval()

        print(
            "[EXIT_CNN]",
            f"device={self.device}",
            f"epoch={checkpoint.get('epoch', '?')}",
            f"model={self.model_path}",
        )

    @torch.inference_mode()
    def classify_patches(self, patches):
        features = exit_patches_to_tensor(patches).to(self.device)
        logits = self.model(features)
        probs = torch.softmax(logits, dim=1)
        conf, idx = probs.max(dim=1)
        idx = idx.cpu().numpy()
        conf = conf.cpu().numpy()
        names = [self.classes[int(i)] for i in idx]
        return names, conf.astype(np.float32)

    def detect(self, frame: np.ndarray, threshold: float = 0.72):
        frame = np.asarray(frame)[:ROOM_H * TILE, :ROOM_W * TILE, :3]
        regions = []
        patches = []
        for direction, (y0, x0, y1, x1) in EXIT_REGIONS:
            regions.append(direction)
            patches.append(frame[y0:y1, x0:x1, :])

        names, confidences = self.classify_patches(patches)

        exits = []
        for direction, name, confidence in zip(regions, names, confidences):
            if name == "none" or float(confidence) < threshold:
                continue
            exit_type, opened = EXIT_INFO[name]
            exits.append(
                {
                    "score": float(1.0 - confidence),
                    "confidence": float(confidence),
                    "direction": direction,
                    "tiles": list(EXIT_TILES_BY_DIR[direction]),
                    "exit_type": exit_type,
                    "opened": bool(opened),
                }
            )
        return exits
