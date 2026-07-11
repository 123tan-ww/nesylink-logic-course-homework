from __future__ import annotations

from pathlib import Path

import numpy as np
import torch
from torch import nn

from Dataclass import (
    BRIDGE,
    BUTTON,
    CHEST,
    CHEST_OPENED,
    EMPTY,
    GAP,
    NPC,
    ROOM_H,
    ROOM_W,
    SWITCH,
    TILE,
    TRAP,
    WALL,
)


class StaticTileCNN(nn.Module):
    def __init__(self, num_terrain_classes: int, num_object_classes: int):
        super().__init__()

        self.backbone = nn.Sequential(
            nn.Conv2d(4, 32, 3, padding=1),
            nn.BatchNorm2d(32),
            nn.ReLU(inplace=True),
            nn.Conv2d(32, 32, 3, padding=1),
            nn.BatchNorm2d(32),
            nn.ReLU(inplace=True),
            nn.MaxPool2d(2),

            nn.Conv2d(32, 64, 3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
            nn.Conv2d(64, 64, 3, padding=1),
            nn.BatchNorm2d(64),
            nn.ReLU(inplace=True),
            nn.MaxPool2d(2),

            nn.Conv2d(64, 128, 3, padding=1),
            nn.BatchNorm2d(128),
            nn.ReLU(inplace=True),
            nn.AdaptiveAvgPool2d((1, 1)),
        )

        self.dropout = nn.Dropout(0.20)
        self.terrain_head = nn.Linear(128, num_terrain_classes)
        self.object_head = nn.Linear(128, num_object_classes)

    def forward(self, x):
        features = self.dropout(self.backbone(x).flatten(1))
        return self.terrain_head(features), self.object_head(features)


def tiles_to_tensor(tiles: np.ndarray) -> torch.Tensor:
    array = np.asarray(tiles)

    if array.ndim != 4 or array.shape[1:] != (TILE, TILE, 3):
        raise ValueError(
            f"Expected (N, {TILE}, {TILE}, 3), got {array.shape}"
        )

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


class StaticTileClassifier:
    TERRAIN_TO_GRID = {
        "floor": EMPTY,
        "wall": WALL,
        "gap": GAP,
        "bridge": BRIDGE,
        "abyss": TRAP,
    }

    OBJECT_TO_GRID = {
        "none": None,
        "chest_closed": CHEST,
        "chest_open": CHEST_OPENED,
        "button_up": BUTTON,
        "button_down": BUTTON,
        "switch_off": SWITCH,
        "switch_on": SWITCH,
        "trap": TRAP,
        "npc": NPC,
    }

    DEFAULT_MODEL_NAMES = (
        "static_tile_cnn_eval_colors.pt",
        "static_tile_cnn_dynamic.pt",
        "static_tile_cnn.pt",
    )

    def __init__(self, model_path=None, device="auto"):
        if model_path is None:
            weights_dir = Path(__file__).resolve().parent / "weights"
            for model_name in self.DEFAULT_MODEL_NAMES:
                candidate = weights_dir / model_name
                if candidate.exists():
                    model_path = candidate
                    break
            else:
                model_path = weights_dir / self.DEFAULT_MODEL_NAMES[0]

        self.model_path = Path(model_path).resolve()

        if not self.model_path.exists():
            raise FileNotFoundError(
                f"Checkpoint not found: {self.model_path}"
            )

        if device == "auto":
            device = "cuda" if torch.cuda.is_available() else "cpu"

        self.device = torch.device(device)

        checkpoint = torch.load(
            self.model_path,
            map_location="cpu",
            weights_only=True,
        )

        self.terrain_classes = list(checkpoint["terrain_classes"])
        self.object_classes = list(checkpoint["object_classes"])

        self.model = StaticTileCNN(
            len(self.terrain_classes),
            len(self.object_classes),
        )
        self.model.load_state_dict(checkpoint["model_state_dict"])
        self.model.to(self.device)
        self.model.eval()

        print(
            "[STATIC_CNN]",
            f"device={self.device}",
            f"epoch={checkpoint.get('epoch', '?')}",
            f"model={self.model_path}",
        )

    def _decode(
        self,
        terrain_index,
        object_index,
        terrain_confidence,
        object_confidence,
    ):
        terrain_name = self.terrain_classes[int(terrain_index)]
        object_name = self.object_classes[int(object_index)]

        if object_name != "none":
            label = self.OBJECT_TO_GRID[object_name]
            name = object_name
        else:
            label = self.TERRAIN_TO_GRID[terrain_name]
            name = terrain_name

        confidence = min(
            float(terrain_confidence),
            float(object_confidence),
        )

        return int(label), name, confidence

    @torch.inference_mode()
    def classify_tiles(self, tiles):
        features = tiles_to_tensor(tiles).to(self.device)

        terrain_logits, object_logits = self.model(features)

        terrain_probs = torch.softmax(terrain_logits, dim=1)
        object_probs = torch.softmax(object_logits, dim=1)

        terrain_conf, terrain_idx = terrain_probs.max(dim=1)
        object_conf, object_idx = object_probs.max(dim=1)

        terrain_conf = terrain_conf.cpu().numpy()
        object_conf = object_conf.cpu().numpy()
        terrain_idx = terrain_idx.cpu().numpy()
        object_idx = object_idx.cpu().numpy()

        labels = np.empty(len(tiles), dtype=np.int64)
        names = []
        confidences = np.empty(len(tiles), dtype=np.float32)

        for i in range(len(tiles)):
            label, name, confidence = self._decode(
                terrain_idx[i],
                object_idx[i],
                terrain_conf[i],
                object_conf[i],
            )
            labels[i] = label
            names.append(name)
            confidences[i] = confidence

        return labels, names, confidences

    def classify_tile(self, patch):
        patch = np.asarray(patch)

        if patch.shape != (TILE, TILE, 3):
            raise ValueError(
                f"Expected ({TILE}, {TILE}, 3), got {patch.shape}"
            )

        labels, names, confidences = self.classify_tiles(
            patch[None, :, :, :]
        )

        legacy_score = (1.0 - float(confidences[0])) * 1000.0

        return int(labels[0]), names[0], legacy_score

    def classify_frame(self, frame):
        frame = np.asarray(frame)
        frame = frame[:ROOM_H * TILE, :ROOM_W * TILE, :3]

        tiles = np.stack(
            [
                frame[
                    y * TILE:(y + 1) * TILE,
                    x * TILE:(x + 1) * TILE,
                    :,
                ]
                for y in range(ROOM_H)
                for x in range(ROOM_W)
            ],
            axis=0,
        )

        labels, names, confidences = self.classify_tiles(tiles)

        return (
            labels.reshape(ROOM_H, ROOM_W),
            np.asarray(names, dtype=object).reshape(ROOM_H, ROOM_W),
            confidences.reshape(ROOM_H, ROOM_W),
        )
