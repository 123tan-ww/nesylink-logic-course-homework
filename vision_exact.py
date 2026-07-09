from __future__ import annotations

from typing import List

import numpy as np

from nesylink.core.constants import (
    COLOR_EXIT_CONDITIONAL,
    COLOR_EXIT_LOCKED,
    COLOR_EXIT_NORMAL,
)
from nesylink.core.rendering import sprites as sp
from nesylink.core.rendering.renderer import MONSTER_COLORS

from Dataclass import (
    BRIDGE,
    BUTTON,
    CHEST,
    CHEST_OPENED,
    EMPTY,
    EXIT,
    ExitInfo,
    GAP,
    MONSTER,
    NPC,
    PLAYER,
    ROOM_H,
    ROOM_W,
    SWITCH,
    TILE,
    TRAP,
    WALL,
    SymbolicObs,
)

TILE_SHAPE = (TILE, TILE, 3)

EXIT_TILES_BY_DIR = {
    "north": [(4, 0), (5, 0)],
    "south": [(4, ROOM_H - 1), (5, ROOM_H - 1)],
    "west": [(0, 3), (0, 4)],
    "east": [(ROOM_W - 1, 3), (ROOM_W - 1, 4)],
}


def blank_tile() -> np.ndarray:
    """
    生成标准地板 tile，用作其它静态模板的背景。
    """
    frame = np.zeros(TILE_SHAPE, dtype=np.uint8)
    sp.draw_floor(frame, 0, 0)
    return frame


def sprite_to_template(sprite, palette):
    """
    将字符画 sprite 转成 RGB 模板和有效像素 mask，透明区域不参与匹配。
    """
    h = len(sprite)
    w = len(sprite[0])
    rgb = np.zeros((h, w, 3), dtype=np.uint8)
    mask = np.zeros((h, w), dtype=bool)
    for yy, row in enumerate(sprite):
        for xx, key in enumerate(row):
            color = palette.get(key)
            if color is not None:
                rgb[yy, xx] = color
                mask[yy, xx] = True
    return rgb, mask


def masked_mse(patch: np.ndarray, rgb: np.ndarray, mask: np.ndarray | None = None) -> float:
    if mask is None:
        mask = np.ones(patch.shape[:2], dtype=bool)
    if mask.sum() == 0:
        return 1e18
    diff = patch.astype(np.float32)[mask] - rgb.astype(np.float32)[mask]
    return float(np.mean(diff * diff))


def make_static_templates():
    # 静态 tile 模板覆盖墙、洞、桥、宝箱、按钮、开关等可规划对象。
    # 桥上宝箱单独建模板，用来识别 task4/task5 这类动态地形上的箱子。
    templates = []

    f = blank_tile()
    templates.append((EMPTY, "floor", f))

    f = blank_tile()
    sp.draw_wall(f, 0, 0)
    templates.append((WALL, "wall", f))

    f = blank_tile()
    sp.draw_gap(f, 0, 0)
    templates.append((GAP, "gap", f))

    f = blank_tile()
    sp.draw_bridge(f, 0, 0)
    templates.append((BRIDGE, "bridge", f))

    for loot in ["key", "gold", "heal", "item", ""]:
        f = blank_tile()
        sp.draw_chest(f, 0, 0, opened=False, loot_kind=loot)
        templates.append((CHEST, f"chest_{loot}", f))

        f = blank_tile()
        sp.draw_chest(f, 0, 0, opened=True, loot_kind=loot)
        templates.append((CHEST_OPENED, f"chest_opened_{loot}", f))

        f = blank_tile()
        sp.draw_bridge(f, 0, 0)
        sp.draw_chest(f, 0, 0, opened=False, loot_kind=loot)
        templates.append((CHEST, f"chest_bridge_{loot}", f))

        f = blank_tile()
        sp.draw_bridge(f, 0, 0)
        sp.draw_chest(f, 0, 0, opened=True, loot_kind=loot)
        templates.append((CHEST_OPENED, f"chest_opened_bridge_{loot}", f))

    for pressed in [False, True]:
        f = blank_tile()
        sp.draw_button(f, 0, 0, pressed=pressed)
        templates.append((BUTTON, f"button_{pressed}", f))

    for activated in [False, True]:
        f = blank_tile()
        sp.draw_switch(f, 0, 0, activated=activated)
        templates.append((SWITCH, f"switch_{activated}", f))

    f = blank_tile()
    sp.draw_trap(f, 0, 0)
    templates.append((TRAP, "trap", f))

    f = blank_tile()
    sp.draw_abyss(f, 0, 0)
    templates.append((TRAP, "abyss", f))

    f = blank_tile()
    sp.draw_npc(f, 0, 0, sp.HIGHLIGHT)
    templates.append((NPC, "npc", f))

    return templates


# 识别静态item
class StaticTileClassifier:
    def __init__(self):
        self.templates = make_static_templates()

    def classify_tile(self, patch: np.ndarray):
        best_label = EMPTY
        best_name = "floor"
        best_score = 1e18
        for label, name, tmpl in self.templates:
            score = masked_mse(patch, tmpl)
            if score < best_score:
                best_score = score
                best_label = label
                best_name = name
        return best_label, best_name, best_score


# 玩家模板匹配：同时识别像素左上角、tile 坐标和朝向。
class PlayerDetector:
    def __init__(self):
        self.templates = []
        for facing, sprite in sp.PLAYER_SPRITES.items():
            rgb, mask = sprite_to_template(sprite, sp.PLAYER_PALETTE)
            self.templates.append((facing, rgb, mask))

    def detect(self, frame: np.ndarray):
        h, w = frame.shape[:2]
        best = {"score": 1e18, "xy": None, "facing": None}
        for facing, rgb, mask in self.templates:
            th, tw = rgb.shape[:2]
            for y in range(0, h - th + 1):
                for x in range(0, w - tw + 1):
                    patch = frame[y:y + th, x:x + tw, :]
                    score = masked_mse(patch, rgb, mask)
                    if score < best["score"]:
                        best = {"score": score, "xy": (x, y), "facing": facing}
        if best["score"] > 1000 or best["xy"] is None:
            return None
        x, y = best["xy"]
        # 用 sprite 中心点映射 tile，比直接用左上角更稳定，尤其是跨 tile 边界时。
        tx = max(0, min(ROOM_W - 1, (x + TILE * 0.5) // TILE))
        ty = max(0, min(ROOM_H - 1, (y + TILE * 0.5) // TILE))
        return {
            "tile": (int(tx), int(ty)),
            "position_px": (float(x), float(y)),
            "facing": best["facing"],
            "score": best["score"],
        }


# 怪物模板匹配：保留像素坐标，供近身战判断 AABB/对齐风险。
class MonsterDetector:
    def __init__(self):
        self.templates = []
        for monster_type, sprite in sp.MONSTER_SPRITES.items():
            color = MONSTER_COLORS[monster_type]
            palette = {
                "O": sp.OUTLINE,
                "M": color,
                "H": sp.MONSTER_DARK,
                "E": sp.MONSTER_EYE,
            }
            rgb, mask = sprite_to_template(sprite, palette)
            self.templates.append((monster_type, rgb, mask))

    def detect_all(self, frame: np.ndarray):
        h, w = frame.shape[:2]
        detections = []
        for monster_type, rgb, mask in self.templates:
            th, tw = rgb.shape[:2]
            for y in range(0, h - th + 1):
                for x in range(0, w - tw + 1):
                    patch = frame[y:y + th, x:x + tw, :]
                    score = masked_mse(patch, rgb, mask)
                    if score < 1000:
                        tx = max(0, min(ROOM_W - 1, (x + 8) // TILE))
                        ty = max(0, min(ROOM_H - 1, (y + 8) // TILE))
                        detections.append((score, monster_type, int(tx), int(ty), float(x), float(y)))

        best_by_tile = {}
        for score, monster_type, tx, ty, x, y in detections:
            # 同一 tile 可能被多个怪物模板命中，保留误差最低的匹配。
            key = (tx, ty)
            if key not in best_by_tile or score < best_by_tile[key][0]:
                best_by_tile[key] = (score, monster_type, x, y)

        return [
            {
                "tile": tile,
                "type": value[1],
                "position_px": (value[2], value[3]),
                "score": value[0],
            }
            for tile, value in best_by_tile.items()
        ]


def make_exit_patch(direction: str, exit_type: str, opened: bool = False):
    if direction in {"west", "east"}:
        patch = np.zeros((32, 16, 3), dtype=np.uint8)
        mask = np.zeros((32, 16), dtype=bool)
        mask[2:30, 2:14] = True
        tiles = ((0, 0), (0, 1))
    else:
        patch = np.zeros((16, 32, 3), dtype=np.uint8)
        mask = np.zeros((16, 32), dtype=bool)
        mask[2:14, 2:30] = True
        tiles = ((0, 0), (1, 0))

    if exit_type == "locked_key":
        color = COLOR_EXIT_LOCKED
    elif exit_type == "conditional":
        color = COLOR_EXIT_CONDITIONAL
    else:
        color = COLOR_EXIT_NORMAL
    sp.draw_exit(patch, tiles, exit_type, color, opened=opened)
    return patch, mask


# 识别出口
class ExitDetector:
    def __init__(self):
        self.templates = []
        for direction in ["north", "south", "west", "east"]:
            for exit_type in ["normal", "locked_key", "conditional"]:
                for opened in [False, True]:
                    patch, mask = make_exit_patch(direction, exit_type, opened)
                    self.templates.append(
                        {
                            "direction": direction,
                            "exit_type": exit_type,
                            "opened": opened,
                            "patch": patch,
                            "mask": mask,
                        }
                    )

    def detect(self, frame: np.ndarray, threshold: float = 500.0):
        fixed_regions = [
            ("north", frame[0:16, 4 * TILE:6 * TILE, :]),
            ("south", frame[7 * TILE:8 * TILE, 4 * TILE:6 * TILE, :]),
            ("west", frame[3 * TILE:5 * TILE, 0:TILE, :]),
            ("east", frame[3 * TILE:5 * TILE, 9 * TILE:10 * TILE, :]),
        ]
        exits = []
        for direction, patch in fixed_regions:
            best = None
            for tmpl in self.templates:
                if tmpl["direction"] != direction:
                    continue
                score = masked_mse(patch, tmpl["patch"], tmpl["mask"])
                if best is None or score < best["score"]:
                    best = {
                        "score": score,
                        "direction": direction,
                        "tiles": list(EXIT_TILES_BY_DIR[direction]),
                        "exit_type": tmpl["exit_type"],
                        "opened": tmpl["opened"],
                    }
            if best is not None and best["score"] < threshold:
                exits.append(best)
        return exits



class PixelPerception:
    def __init__(self):
        # 感知模块只读取 raw pixels：先分类静态 tile，再覆盖玩家/怪物/出口等动态对象。
        self.static_clf = StaticTileClassifier()
        self.player_detector = PlayerDetector()
        self.monster_detector = MonsterDetector()
        self.exit_detector = ExitDetector()

    def __call__(self, obs):
        # 输入可能包含 HUD，这里只取上方 128x160 的地图区域。
        frame = np.asarray(obs)[:128, :160, :3]
        grid = np.zeros((ROOM_H, ROOM_W), dtype=np.int64)

        for y in range(ROOM_H):
            for x in range(ROOM_W):
                patch = frame[y * TILE:(y + 1) * TILE, x * TILE:(x + 1) * TILE, :]
                label, _name, score = self.static_clf.classify_tile(patch)
                grid[y, x] = label if score <= 700 else EMPTY

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

        player_info = self.player_detector.detect(frame)
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
        for m in self.monster_detector.detect_all(frame):
            # tile 坐标用于规划，像素坐标用于战斗距离和对齐判断。
            tx, ty = m["tile"]
            monsters.append((tx, ty))
            monsters_px.append(m["position_px"])
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
                v = int(grid[y, x])
                if v == CHEST:
                    chests.append((x, y))
                elif v == TRAP:
                    traps.append((x, y))
                elif v == BUTTON:
                    buttons.append((x, y))
                elif v == SWITCH:
                    switches.append((x, y))
                elif v == EXIT and (x, y) not in exits:
                    exits.append((x, y))
                    exit_types.setdefault((x, y), "unknown")
                    exit_opened.setdefault((x, y), False)

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
