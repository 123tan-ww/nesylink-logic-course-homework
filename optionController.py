from __future__ import annotations

from typing import List, Optional

from nesylink.core.constants import (
    ACTION_A,
    ACTION_B,
    ACTION_DOWN,
    ACTION_LEFT,
    ACTION_NOOP,
    ACTION_RIGHT,
    ACTION_UP,
)

from Dataclass import ROOM_H, ROOM_W, TILE_SIZE, BeliefState, ExitInfo, Pos, Subgoal, SymbolicObs
from symbolicPlanner import adjacent_tiles, astar_path, in_bounds, is_passable, manhattan, nearest_tile, neighbors


def repeat_action(action: int, n: int) -> List[int]:
    return [action] * n


def expand_tile_actions(
    tile_actions: List[int],
    start_tile: Optional[Pos] = None,
    start_px: Optional[tuple[float, float]] = None,
) -> List[int]:
    """
    把 tile 级路径展开成像素级动作；转弯前先对齐到当前 tile 的左上角，
    避免在门框、墙角和窄通道中因为半格偏移而被碰撞体挡住。
    """
    actions: List[int] = []
    px = [float(start_px[0]), float(start_px[1])] if start_px is not None else None

    def current_tile() -> Pos:
        if px is None:
            return start_tile if start_tile is not None else (0, 0)
        tx = int(max(0, min(ROOM_W - 1, (px[0] + TILE_SIZE * 0.5) // TILE_SIZE)))
        ty = int(max(0, min(ROOM_H - 1, (px[1] + TILE_SIZE * 0.5) // TILE_SIZE)))
        return tx, ty

    def append_alignment(axis: str, target: float) -> None:
        if px is None:
            return
        index = 0 if axis == "x" else 1
        delta = int(round(target - px[index]))
        if delta == 0:
            return
        if axis == "x":
            action = ACTION_RIGHT if delta > 0 else ACTION_LEFT
        else:
            action = ACTION_DOWN if delta > 0 else ACTION_UP
        actions.extend(repeat_action(action, abs(delta)))
        px[index] = target

    for action in tile_actions:
        if px is not None:
            tx, ty = current_tile()
            if action in {ACTION_UP, ACTION_DOWN}:
                append_alignment("x", float(tx * TILE_SIZE))
            elif action in {ACTION_LEFT, ACTION_RIGHT}:
                append_alignment("y", float(ty * TILE_SIZE))
        actions.extend(repeat_action(action, TILE_SIZE))
        if px is not None:
            if action == ACTION_LEFT:
                px[0] -= TILE_SIZE
            elif action == ACTION_RIGHT:
                px[0] += TILE_SIZE
            elif action == ACTION_UP:
                px[1] -= TILE_SIZE
            elif action == ACTION_DOWN:
                px[1] += TILE_SIZE
    return actions


def expand_from_sym(sym: SymbolicObs, tile_actions: List[int]) -> List[int]:
    """
    基于当前视觉中的玩家像素坐标展开路径。
    """
    return expand_tile_actions(tile_actions, sym.player, sym.player_px)


def action_to_face(src: Pos, dst: Pos) -> int:
    """
    计算从 src 面向相邻目标 dst 所需的方向动作。
    """
    sx, sy = src
    dx, dy = dst
    if dx > sx:
        return ACTION_RIGHT
    if dx < sx:
        return ACTION_LEFT
    if dy > sy:
        return ACTION_DOWN
    if dy < sy:
        return ACTION_UP
    return ACTION_NOOP


def action_to_name(action: int) -> str:
    """
    把环境动作编号转换成内部朝向字符串。
    """
    if action == ACTION_UP:
        return "up"
    if action == ACTION_DOWN:
        return "down"
    if action == ACTION_LEFT:
        return "left"
    if action == ACTION_RIGHT:
        return "right"
    return "none"


def get_exit_info_for_tile(sym: SymbolicObs, tile: Pos) -> Optional[ExitInfo]:
    """
    根据出口 tile 找到对应的出口描述。
    """
    for info in sym.exit_infos:
        if tile in info.tiles:
            return info
    return None


def exit_out_action(info: ExitInfo) -> int:
    """
    出口方向对应的持续移动动作。
    """
    if info.direction == "north":
        return ACTION_UP
    if info.direction == "south":
        return ACTION_DOWN
    if info.direction == "west":
        return ACTION_LEFT
    if info.direction == "east":
        return ACTION_RIGHT
    return ACTION_NOOP


def exit_approach_tiles(info: ExitInfo) -> List[Pos]:
    """
    出口内侧可站立的邻接格；到达这些格后继续朝出口方向移动即可换房。
    """
    result: List[Pos] = []
    for x, y in info.tiles:
        if info.direction == "north":
            p = (x, y + 1)
        elif info.direction == "south":
            p = (x, y - 1)
        elif info.direction == "west":
            p = (x + 1, y)
        elif info.direction == "east":
            p = (x - 1, y)
        else:
            continue
        if in_bounds(p) and p not in result:
            result.append(p)
    return result


class OptionController:
    def build_actions(
        self,
        sym: SymbolicObs,
        belief: BeliefState,
        subgoal: Subgoal,
    ) -> List[int]:
        if sym.player is None:
            return [ACTION_NOOP]
        if subgoal.kind == "wait":
            return [ACTION_NOOP]
        if subgoal.kind == "find_chest" and subgoal.target is not None:
            return self.actions_to_interactable(sym, belief, subgoal.target)
        if subgoal.kind == "attack_monster" and subgoal.target is not None:
            return self.actions_attack_monster(sym, belief, subgoal.target)
        if subgoal.kind == "press_button" and subgoal.target is not None:
            return self.actions_press_button(sym, subgoal.target)
        if subgoal.kind == "activate_switch" and subgoal.target is not None:
            return self.actions_to_interactable(sym, belief, subgoal.target)
        if subgoal.kind == "go_exit" and subgoal.target is not None:
            return self.actions_to_exit(sym, subgoal.target)
        if subgoal.kind == "explore":
            return self.actions_explore(sym)
        return [ACTION_NOOP]

    def actions_press_button(self, sym: SymbolicObs, button_pos: Pos) -> List[int]:
        """
        按钮需要踩上去触发，因此直接规划到按钮所在 tile。
        """
        assert sym.player is not None
        if sym.player == button_pos:
            return [ACTION_NOOP]
        tile_actions = astar_path(sym.grid, sym.player, button_pos, sym)
        if not tile_actions:
            return [ACTION_NOOP]
        return expand_from_sym(sym, tile_actions)

    def actions_to_interactable(
        self,
        sym: SymbolicObs,
        belief: BeliefState,
        obj_pos: Pos,
    ) -> List[int]:
        """
        宝箱/开关只要求相邻即可按 A 交互，因此规划到最近的可达邻接格。
        """
        del belief
        assert sym.player is not None
        candidates = []
        for p in adjacent_tiles(obj_pos):
            if not in_bounds(p):
                continue
            x, y = p
            if not is_passable(int(sym.grid[y, x])):
                continue
            path = astar_path(sym.grid, sym.player, p, sym)
            if not path and sym.player != p:
                continue
            face_action = action_to_face(p, obj_pos)
            candidates.append((len(path), p, path, face_action))

        if not candidates:
            return [ACTION_NOOP]

        candidates.sort(key=lambda item: item[0])
        _score, target_adj, tile_actions, face_action = candidates[0]
        actions = expand_from_sym(sym, tile_actions)
        if sym.player == target_adj or tile_actions:
            actions.extend([ACTION_A] * 3)
        return actions or [ACTION_NOOP]

    def actions_attack_monster(
        self,
        sym: SymbolicObs,
        belief: BeliefState,
        monster_pos: Pos,
    ) -> List[int]:
        """
        生成击怪动作。战斗比普通交互更严格：必须面向怪物后才能用剑命中。
        """
        assert sym.player is not None
        player = sym.player
        if manhattan(player, monster_pos) == 1:
            # 贴脸时不再继续走路；未面向先举盾再转向，降低被怪物碰撞扣血的概率。
            face_action = action_to_face(player, monster_pos)
            actions: List[int] = []
            if face_action != ACTION_NOOP and belief.facing != action_to_name(face_action):
                actions.append(ACTION_B)
                actions.append(face_action)
            actions.append(ACTION_A)
            return actions

        candidates = []
        for p in adjacent_tiles(monster_pos):
            if not in_bounds(p):
                continue
            x, y = p
            if not is_passable(int(sym.grid[y, x])):
                continue
            path = astar_path(sym.grid, player, p, sym)
            if not path and player != p:
                continue
            face_action = action_to_face(p, monster_pos)
            orientation_penalty = 5 if path and path[-1] != face_action else 0
            candidates.append((len(path) + orientation_penalty, p, path, face_action))

        if not candidates:
            return [ACTION_NOOP]
        candidates.sort(key=lambda item: item[0])
        _score, _target_adj, tile_actions, face_action = candidates[0]

        # 怪物会移动，长路径很容易过期；每次最多推进两个 tile，然后重新感知规划。
        chunk = tile_actions[:2] if sym.monsters else tile_actions
        actions = expand_from_sym(sym, chunk)
        if len(chunk) == len(tile_actions):
            if face_action != ACTION_NOOP and action_to_name(face_action) != sym.facing:
                actions.append(face_action)
            actions.append(ACTION_A)
        return actions or [ACTION_NOOP]

    def actions_to_exit(self, sym: SymbolicObs, exit_pos: Pos) -> List[int]:
        """
        先到出口内侧邻接格，再持续朝出口方向移动直到触发换房。
        """
        assert sym.player is not None
        info = get_exit_info_for_tile(sym, exit_pos)
        if info is not None:
            out_action = exit_out_action(info)
            candidates = []
            for p in exit_approach_tiles(info):
                x, y = p
                if not is_passable(int(sym.grid[y, x])):
                    continue
                path = astar_path(sym.grid, sym.player, p, sym)
                if not path and sym.player != p:
                    continue
                candidates.append((len(path), p, path))
            if candidates:
                candidates.sort(key=lambda item: item[0])
                _score, approach, tile_actions = candidates[0]
                if sym.player == approach:
                    return [out_action] * 72
                actions = expand_from_sym(sym, tile_actions)
                actions.extend([out_action] * 72)
                return actions

        tile_actions = astar_path(sym.grid, sym.player, exit_pos, sym)
        actions = expand_from_sym(sym, tile_actions)
        out_action = self.exit_direction_from_tile(exit_pos)
        if out_action != ACTION_NOOP:
            actions.extend([out_action] * 72)
        return actions or [ACTION_NOOP]

    def actions_explore(self, sym: SymbolicObs) -> List[int]:
        """
        没有明确子目标时的保底探索：优先尝试视觉可见出口，否则走向任一可通行邻格。
        """
        assert sym.player is not None
        for info in sym.exit_infos:
            target = nearest_tile(sym.player, info.tiles)
            if target is not None:
                return self.actions_to_exit(sym, target)
        for nxt, action in neighbors(sym.player):
            if not in_bounds(nxt):
                continue
            x, y = nxt
            if is_passable(int(sym.grid[y, x])):
                return expand_from_sym(sym, [action])
        return [ACTION_NOOP]

    def exit_direction_from_tile(self, exit_pos: Pos) -> int:
        """
        Determine the action needed to exit through a given tile position based on its location in the room.
        """
        x, y = exit_pos
        if y == 0:
            return ACTION_UP
        if y == ROOM_H - 1:
            return ACTION_DOWN
        if x == 0:
            return ACTION_LEFT
        if x == ROOM_W - 1:
            return ACTION_RIGHT
        return ACTION_NOOP
