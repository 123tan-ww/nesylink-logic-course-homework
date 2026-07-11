from __future__ import annotations

from typing import List

import numpy as np

from Dataclass import (
    BUTTON,
    CHEST,
    CHEST_OPENED,
    EMPTY,
    EXIT,
    ExitInfo,
    MONSTER,
    NPC,
    PLAYER,
    ROOM_H,
    ROOM_W,
    SWITCH,
    TILE,
    TRAP,
    SymbolicObs,
)
from cnn_dynamic_detector import DynamicObjectDetector
from cnn_exit_classifier import ExitRegionClassifier
from cnn_static_classifier import StaticTileClassifier


class ExitDetector:
    def __init__(self):
        self.classifier = ExitRegionClassifier()

    def detect(self, frame: np.ndarray, threshold: float = 0.72):
        return self.classifier.detect(frame, threshold=threshold)


class PixelPerception:
    def __init__(self):
        # Online perception uses learned classifiers on raw pixels only.
        self.static_clf = StaticTileClassifier()
        self.dynamic_detector = DynamicObjectDetector()
        self.exit_detector = ExitDetector()

    def __call__(self, obs):
        frame = np.asarray(obs)[:ROOM_H * TILE, :ROOM_W * TILE, :3]

        grid = np.zeros((ROOM_H, ROOM_W), dtype=np.int64)
        static_grid, _static_names, static_confidences = self.static_clf.classify_frame(frame)

        confidence_threshold = 0.80
        grid[:, :] = np.where(
            static_confidences >= confidence_threshold,
            static_grid,
            EMPTY,
        )

        exit_infos: List[ExitInfo] = []
        exits = []
        exit_types = {}
        exit_opened = {}
        for e in self.exit_detector.detect(frame):
            info = ExitInfo(
                tiles=[tuple(tile) for tile in e["tiles"]],
                direction=e["direction"],
                exit_type=e["exit_type"],
                opened=bool(e["opened"]),
                score=float(e["score"]),
            )
            exit_infos.append(info)
            for x, y in info.tiles:
                p = (int(x), int(y))
                exits.append(p)
                exit_types[p] = info.exit_type
                exit_opened[p] = info.opened
                grid[y, x] = EXIT

        dynamic = self.dynamic_detector.detect(frame)
        player_info = dynamic["player"]
        player = None
        player_px = None
        facing = "down"
        if player_info is not None:
            player = player_info["tile"]
            player_px = player_info["position_px"]
            facing = player_info["facing"]
            px, py = player
            grid[py, px] = PLAYER

        monsters = []
        monsters_px = []
        for monster_info in dynamic["monsters"]:
            tx, ty = monster_info["tile"]
            monsters.append((tx, ty))
            monsters_px.append(monster_info["position_px"])
            grid[ty, tx] = MONSTER

        return self.grid_to_symbolic(
            grid=grid,
            player=player,
            player_px=player_px,
            facing=facing,
            monsters=monsters,
            monsters_px=monsters_px,
            exits=exits,
            exit_infos=exit_infos,
            exit_types=exit_types,
            exit_opened=exit_opened,
        )

    def grid_to_symbolic(
        self,
        *,
        grid,
        player,
        player_px,
        facing,
        monsters,
        monsters_px,
        exits,
        exit_infos,
        exit_types,
        exit_opened,
    ):
        chests = []
        traps = []
        buttons = []
        switches = []

        for y in range(ROOM_H):
            for x in range(ROOM_W):
                value = int(grid[y, x])
                if value == CHEST:
                    chests.append((x, y))
                elif value == CHEST_OPENED:
                    continue
                elif value == TRAP:
                    traps.append((x, y))
                elif value == BUTTON:
                    buttons.append((x, y))
                elif value == SWITCH:
                    switches.append((x, y))
                elif value == EXIT and (x, y) not in exits:
                    exits.append((x, y))
                    exit_types.setdefault((x, y), "unknown")
                    exit_opened.setdefault((x, y), False)
                elif value == NPC:
                    continue

        return SymbolicObs(
            grid=grid,
            player=player,
            player_px=player_px,
            facing=facing,
            monsters=monsters,
            monsters_px=monsters_px,
            chests=chests,
            exits=exits,
            exit_infos=exit_infos,
            exit_types=exit_types,
            exit_opened=exit_opened,
            traps=traps,
            buttons=buttons,
            switches=switches,
        )
