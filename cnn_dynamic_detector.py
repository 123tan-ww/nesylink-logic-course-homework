from __future__ import annotations

from pathlib import Path

import numpy as np
import torch
from torch import nn

from Dataclass import ROOM_H, ROOM_W, TILE


DYNAMIC_CLASSES = (
    "none",
    "player_up",
    "player_down",
    "player_left",
    "player_right",
    "monster_chaser",
    "monster_patroller",
    "monster_ambusher",
)

DYNAMIC_PAD = TILE // 2
DYNAMIC_CROP = TILE + DYNAMIC_PAD * 2
OFFSET_BINS = TILE


def _clamp_position_px(left: float, top: float) -> tuple[float, float]:
    max_left = float((ROOM_W - 1) * TILE)
    max_top = float((ROOM_H - 1) * TILE)
    return (
        max(0.0, min(max_left, left)),
        max(0.0, min(max_top, top)),
    )


def _normalize_position_px(left: float, top: float) -> tuple[float, float]:
    left, top = _clamp_position_px(left, top)
    return _clamp_position_px(float(round(left)), float(round(top)))


class DynamicObjectCNN(nn.Module):
    def __init__(self, num_classes: int, offset_mode: str = "regression"):
        super().__init__()
        if offset_mode not in {"regression", "discrete"}:
            raise ValueError(f"Unknown offset_mode: {offset_mode}")
        self.offset_mode = offset_mode
        self.features = nn.Sequential(
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
            nn.Conv2d(128, 128, 3, padding=1),
            nn.BatchNorm2d(128),
            nn.ReLU(inplace=True),
            nn.AdaptiveAvgPool2d((1, 1)),
        )
        self.dropout = nn.Dropout(0.18)
        self.classifier = nn.Linear(128, num_classes)
        if self.offset_mode == "discrete":
            self.offset_x_head = nn.Linear(128, OFFSET_BINS)
            self.offset_y_head = nn.Linear(128, OFFSET_BINS)
        else:
            self.offset_head = nn.Linear(128, 2)

    def forward(self, x):
        features = self.dropout(self.features(x).flatten(1))
        logits = self.classifier(features)
        if self.offset_mode == "discrete":
            return logits, (self.offset_x_head(features), self.offset_y_head(features))
        return logits, torch.sigmoid(self.offset_head(features))


def dynamic_patches_to_tensor(patches) -> torch.Tensor:
    array = np.asarray(patches)
    if array.ndim != 4 or array.shape[1:] != (DYNAMIC_CROP, DYNAMIC_CROP, 3):
        raise ValueError(
            f"Expected (N, {DYNAMIC_CROP}, {DYNAMIC_CROP}, 3), got {array.shape}"
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


def crop_dynamic_patches(frame: np.ndarray) -> tuple[np.ndarray, list[tuple[int, int]]]:
    frame = np.asarray(frame)[:ROOM_H * TILE, :ROOM_W * TILE, :3]
    if frame.shape != (ROOM_H * TILE, ROOM_W * TILE, 3):
        raise ValueError(f"Expected map frame {(ROOM_H * TILE, ROOM_W * TILE, 3)}, got {frame.shape}")

    padded = np.pad(
        frame.astype(np.uint8, copy=False),
        ((DYNAMIC_PAD, DYNAMIC_PAD), (DYNAMIC_PAD, DYNAMIC_PAD), (0, 0)),
        mode="constant",
        constant_values=0,
    )

    patches = []
    tiles = []
    for row in range(ROOM_H):
        for col in range(ROOM_W):
            y0 = row * TILE
            x0 = col * TILE
            patches.append(padded[y0:y0 + DYNAMIC_CROP, x0:x0 + DYNAMIC_CROP, :])
            tiles.append((col, row))

    return np.stack(patches, axis=0), tiles


class DynamicObjectDetector:
    DEFAULT_MODEL_NAME = "dynamic_object_cnn.pt"

    def __init__(self, model_path=None, device="auto"):
        if model_path is None:
            model_path = (
                Path(__file__).resolve().parent
                / "weights"
                / self.DEFAULT_MODEL_NAME
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
        if tuple(self.classes) != DYNAMIC_CLASSES:
            raise ValueError(f"Unexpected dynamic classes: {self.classes}")
        self.offset_mode = str(checkpoint.get("offset_mode", "regression"))

        self.model = DynamicObjectCNN(len(self.classes), offset_mode=self.offset_mode)
        self.model.load_state_dict(checkpoint["model_state_dict"])
        self.model.to(self.device)
        self.model.eval()

        print(
            "[DYNAMIC_CNN]",
            f"device={self.device}",
            f"epoch={checkpoint.get('epoch', '?')}",
            f"offset={self.offset_mode}",
            f"model={self.model_path}",
        )

    @torch.inference_mode()
    def classify_frame(self, frame: np.ndarray):
        patches, tiles = crop_dynamic_patches(frame)
        features = dynamic_patches_to_tensor(patches).to(self.device)
        logits, raw_offsets = self.model(features)
        probs = torch.softmax(logits, dim=1)
        conf, idx = probs.max(dim=1)
        if self.offset_mode == "discrete":
            offset_x_logits, offset_y_logits = raw_offsets
            offset_x = offset_x_logits.argmax(dim=1).float() / float(TILE - 1)
            offset_y = offset_y_logits.argmax(dim=1).float() / float(TILE - 1)
            offsets = torch.stack((offset_x, offset_y), dim=1)
        else:
            offsets = raw_offsets

        return (
            tiles,
            [self.classes[int(i)] for i in idx.cpu().numpy()],
            conf.cpu().numpy().astype(np.float32),
            offsets.cpu().numpy().astype(np.float32),
        )

    def detect(
        self,
        frame: np.ndarray,
        *,
        player_threshold: float = 0.68,
        monster_threshold: float = 0.62,
        monster_nms_distance: float = 10.0,
    ) -> dict[str, object]:
        tiles, names, confidences, offsets = self.classify_frame(frame)

        player = None
        monsters = []

        for tile, name, confidence, offset in zip(tiles, names, confidences, offsets):
            if name == "none":
                continue

            col, row = tile
            rel_x = float(np.clip(offset[0], 0.0, 1.0) * (TILE - 1))
            rel_y = float(np.clip(offset[1], 0.0, 1.0) * (TILE - 1))
            left = float(col * TILE - DYNAMIC_PAD + rel_x)
            top = float(row * TILE - DYNAMIC_PAD + rel_y)
            left, top = _normalize_position_px(left, top)

            detection = {
                "tile": (int(col), int(row)),
                "position_px": (left, top),
                "confidence": float(confidence),
                "score": float(1.0 - confidence),
            }

            if name.startswith("player_"):
                if float(confidence) < player_threshold:
                    continue
                facing = name.removeprefix("player_")
                candidate = {**detection, "facing": facing}
                if player is None or candidate["confidence"] > player["confidence"]:
                    player = candidate
                continue

            if name.startswith("monster_"):
                if float(confidence) < monster_threshold:
                    continue
                monsters.append(
                    {**detection, "type": name.removeprefix("monster_")}
                )

        monsters.sort(key=lambda item: item["confidence"], reverse=True)
        selected_monsters = []
        for monster in monsters:
            mx, my = monster["position_px"]
            duplicate = False
            for kept in selected_monsters:
                kx, ky = kept["position_px"]
                if float(np.hypot(mx - kx, my - ky)) < monster_nms_distance:
                    duplicate = True
                    break
            if not duplicate:
                selected_monsters.append(monster)

        return {"player": player, "monsters": selected_monsters}
