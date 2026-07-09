from __future__ import annotations

from typing import Tuple

from nesylink.core.constants import (
    ACTION_DOWN,
    ACTION_LEFT,
    ACTION_NOOP,
    ACTION_RIGHT,
    ACTION_UP,
)

from Dataclass import GAP, MONSTER, ROOM_H, ROOM_W, TILE_SIZE, TRAP, WALL, BeliefState, Pos, SymbolicObs
from symbolicPlanner import MOVE_ACTIONS, in_bounds, is_passable


class SafetyShield:
    def filter(self, action: int, sym: SymbolicObs, belief: BeliefState) -> Tuple[int, bool]:
        # 保守动作过滤：根据当前视觉符号图阻止走进墙、陷阱、缺口和怪物。
        # 不依赖 action_blocked 反馈，因此可作为形式化安全层来解释。
        del belief
        if sym.player is None:
            return ACTION_NOOP, True
        if action not in MOVE_ACTIONS:
            return action, True
        if self.is_exit_leaving_action(sym.player, action, sym.exits):
            return action, True
        if self.is_pixel_alignment_move(sym, action):
            # 对齐动作仍留在当前 tile 内，允许执行，否则会在半格偏移时无法修正。
            return action, True

        nxt = self.predict_next_tile(sym.player, action)
        if not in_bounds(nxt):
            return ACTION_NOOP, True

        x, y = nxt
        tile = int(sym.grid[y, x])
        if tile in {WALL, TRAP, GAP, MONSTER} or not is_passable(tile):
            return ACTION_NOOP, True
        return action, True

    def is_pixel_alignment_move(self, sym: SymbolicObs, action: int, tolerance: float = 0.5) -> bool:
        """
        判断该动作是否只是把玩家拉回当前 tile 的对齐位置。
        """
        if sym.player is None or sym.player_px is None:
            return False
        tx, ty = sym.player
        px, py = sym.player_px
        target_x = tx * TILE_SIZE
        target_y = ty * TILE_SIZE
        if action == ACTION_LEFT and px > target_x + tolerance:
            return True
        if action == ACTION_RIGHT and px < target_x - tolerance:
            return True
        if action == ACTION_UP and py > target_y + tolerance:
            return True
        if action == ACTION_DOWN and py < target_y - tolerance:
            return True
        return False

    def predict_next_tile(self, pos: Pos, action: int) -> Pos:
        """
        用 tile 级模型预测下一格，用于静态危险过滤。
        """
        x, y = pos
        if action == ACTION_UP:
            return (x, y - 1)
        if action == ACTION_DOWN:
            return (x, y + 1)
        if action == ACTION_LEFT:
            return (x - 1, y)
        if action == ACTION_RIGHT:
            return (x + 1, y)
        return pos

    def is_exit_leaving_action(self, pos: Pos, action: int, exits: list[Pos]) -> bool:
        """
        离开房间必须允许继续朝边界走，否则会被越界过滤挡住。
        """
        x, y = pos
        if pos not in exits:
            return False
        return (
            (y == 0 and action == ACTION_UP)
            or (y == ROOM_H - 1 and action == ACTION_DOWN)
            or (x == 0 and action == ACTION_LEFT)
            or (x == ROOM_W - 1 and action == ACTION_RIGHT)
        )
