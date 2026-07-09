from __future__ import annotations

from typing import Dict, List, Optional, Tuple
import heapq

import numpy as np

from nesylink.core.constants import (
    ACTION_DOWN,
    ACTION_LEFT,
    ACTION_RIGHT,
    ACTION_UP,
)

from Dataclass import (
    BRIDGE,
    BUTTON,
    EMPTY,
    EXIT,
    MONSTER,
    PLAYER,
    ROOM_H,
    ROOM_W,
    SWITCH,
    TRAP,
    WALL,
    BeliefState,
    Candidate,
    ExitInfo,
    Pos,
    Subgoal,
    SymbolicObs,
    room_signature,
)

MOVE_ACTIONS = {ACTION_UP, ACTION_DOWN, ACTION_LEFT, ACTION_RIGHT}
PASSABLE = {EMPTY, PLAYER, EXIT, BUTTON, BRIDGE, SWITCH}


def neighbors(p: Pos) -> List[Tuple[Pos, int]]:
    x, y = p
    return [
        ((x, y - 1), ACTION_UP),
        ((x, y + 1), ACTION_DOWN),
        ((x - 1, y), ACTION_LEFT),
        ((x + 1, y), ACTION_RIGHT),
    ]


def in_bounds(p: Pos) -> bool:
    x, y = p
    return 0 <= x < ROOM_W and 0 <= y < ROOM_H


def manhattan(a: Pos, b: Pos) -> int:
    return abs(a[0] - b[0]) + abs(a[1] - b[1])


def adjacent_tiles(pos: Pos) -> List[Pos]:
    x, y = pos
    return [(x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y)]


def is_passable(tile: int) -> bool:
    return tile in PASSABLE


def tile_risk_cost(pos: Pos, sym: SymbolicObs) -> float:
    # A* 的软风险项：不完全禁止靠近怪物/陷阱，但会优先选择更安全的路。
    x, y = pos
    cost = 0.0
    for mx, my in sym.monsters:
        d = abs(mx - x) + abs(my - y)
        if d == 0:
            cost += 100.0
        elif d == 1:
            cost += 10.0
        elif d == 2:
            cost += 3.0
    for tx, ty in sym.traps:
        d = abs(tx - x) + abs(ty - y)
        if d == 0:
            cost += 100.0
        elif d == 1:
            cost += 4.0
    return cost


def astar_path(
    grid: np.ndarray,
    start: Pos,
    goal: Pos,
    sym: Optional[SymbolicObs] = None,
) -> List[int]:
    # 在符号网格上规划 tile 路径，返回方向动作列表；像素级展开由 OptionController 完成。
    if start == goal:
        return []

    open_heap = [(0.0, 0.0, start)]
    parent: Dict[Pos, Tuple[Optional[Pos], Optional[int]]] = {start: (None, None)}
    g_score: Dict[Pos, float] = {start: 0.0}

    while open_heap:
        _f, cur_g, cur = heapq.heappop(open_heap)
        if cur == goal:
            actions: List[int] = []
            p = cur
            while parent[p][0] is not None:
                prev, action = parent[p]
                actions.append(action)
                p = prev
            actions.reverse()
            return actions
        if cur_g > g_score.get(cur, float("inf")):
            continue

        for nxt, action in neighbors(cur):
            if not in_bounds(nxt):
                continue
            x, y = nxt
            tile = int(grid[y, x])
            if not is_passable(tile):
                continue
            step_cost = 1.0 + (tile_risk_cost(nxt, sym) if sym is not None else 0.0)
            new_g = cur_g + step_cost
            if new_g < g_score.get(nxt, float("inf")):
                g_score[nxt] = new_g
                parent[nxt] = (cur, action)
                heapq.heappush(open_heap, (new_g + manhattan(nxt, goal), new_g, nxt))

    return []


def nearest_tile(start: Pos, candidates: List[Pos]) -> Optional[Pos]:
    if not candidates:
        return None
    return min(candidates, key=lambda p: manhattan(start, p))


class SymbolicPlanner:
    def next_subgoal(self, sym: SymbolicObs, belief: BeliefState) -> Subgoal:
        # 把当前可见对象都转成候选子目标，再用 value - distance - risk 打分。
        if sym.player is None:
            return Subgoal("wait")

        candidates: List[Candidate] = []

        for monster in sym.monsters:
            candidates.append(
                self.make_candidate(
                    sym,
                    belief,
                    "attack_monster",
                    monster,
                    self.monster_value(sym, belief, monster),
                )
            )

        for chest in sym.chests:
            candidates.append(self.make_candidate(sym, belief, "find_chest", chest, 150.0))

        for button in sym.buttons:
            if button in belief.pressed_buttons:
                continue
            candidates.append(self.make_candidate(sym, belief, "press_button", button, 80.0))

        for switch in sym.switches:
            if switch in belief.activated_switches:
                continue
            switch_value = 75.0 if (belief.keys > 0 or belief.has_sword) else 25.0
            candidates.append(self.make_candidate(sym, belief, "activate_switch", switch, switch_value))

        for info in sym.exit_infos:
            if not self.exit_is_usable(sym, belief, info):
                continue
            target = nearest_tile(sym.player, info.tiles)
            if target is None:
                continue
            value = self.exit_value(sym, belief, info)
            candidates.append(self.make_candidate(sym, belief, "go_exit", target, value))

        reachable = [c for c in candidates if c.dist < 999.0 and c.value > -900.0]
        if reachable:
            return max(reachable, key=lambda c: c.score).subgoal
        return Subgoal("explore")

    def monster_value(self, sym: SymbolicObs, belief: BeliefState, monster: Pos) -> float:
        # 杀怪收益不是固定的：有些怪挡路或守箱必须处理，有些远处怪会拖慢 task5。
        if not belief.has_sword:
            return -999.0
        if sym.player is None:
            return 120.0

        distance_to_player = manhattan(sym.player, monster)
        room = belief.rooms.get(room_signature(sym))
        opened_chest_here = bool(room is not None and room.opened_chests)

        if any(info.exit_type == "conditional" for info in sym.exit_infos):
            # 条件门常要求清怪/按机关；在这类房间里怪物通常是进度瓶颈。
            return 165.0

        if sym.chests:
            # 有可见箱子时，只优先处理贴近玩家或守在箱子附近的怪。
            distance_to_chest = min(manhattan(monster, chest) for chest in sym.chests)
            if distance_to_player <= 1:
                return 170.0
            if distance_to_player <= 3 or distance_to_chest <= 2:
                return 155.0
            return 70.0

        if opened_chest_here and len(sym.exit_infos) <= 1:
            # 单出口房间开完箱后，远处游荡怪通常不是必要目标，优先离开。
            return 125.0 if distance_to_player <= 1 else -999.0

        if opened_chest_here and any(self.exit_is_usable(sym, belief, info) for info in sym.exit_infos):
            # 多出口房间开过箱后，只在怪物贴近时处理，否则探索出口更重要。
            return 145.0 if distance_to_player <= 2 else 25.0

        # 没有可见箱且本房间还没开过箱时，怪物可能守着进度或击杀后揭示隐藏箱。
        return 160.0

    def make_candidate(
        self,
        sym: SymbolicObs,
        belief: BeliefState,
        kind: str,
        target: Pos,
        value: float,
    ) -> Candidate:
        # 攻击目标允许承担一点风险；普通移动/开箱更强调避险。
        dist = self.estimate_distance(sym, kind, target)
        risk = self.estimate_risk(sym, target)
        if kind == "attack_monster":
            score = value - 0.35 * dist - 0.7 * risk
        else:
            score = value - 0.45 * dist - 1.8 * risk
        return Candidate(Subgoal(kind, target), value, dist, risk, score)

    def estimate_distance(self, sym: SymbolicObs, kind: str, target: Pos) -> float:
        # 交互/攻击目标不可站上去，因此估计到目标邻接格的最短距离。
        if sym.player is None:
            return 999.0

        if kind in {"attack_monster", "find_chest", "activate_switch"}:
            best = 999.0
            for p in adjacent_tiles(target):
                if not in_bounds(p):
                    continue
                x, y = p
                if not is_passable(int(sym.grid[y, x])):
                    continue
                path = astar_path(sym.grid, sym.player, p, sym)
                if path or sym.player == p:
                    best = min(best, float(len(path)))
            return best

        path = astar_path(sym.grid, sym.player, target, sym)
        if not path and sym.player != target:
            return 999.0
        return float(len(path))

    def estimate_risk(self, sym: SymbolicObs, target: Pos) -> float:
        risk = 0.0
        for monster in sym.monsters:
            d = manhattan(target, monster)
            if d <= 1:
                risk += 4.0
            elif d == 2:
                risk += 1.5
        for trap in sym.traps:
            d = manhattan(target, trap)
            if d == 0:
                risk += 100.0
            elif d == 1:
                risk += 2.0
        return risk

    def exit_is_usable(self, sym: SymbolicObs, belief: BeliefState, info: ExitInfo) -> bool:
        # 只根据视觉出口类型和已知物品/按钮状态判断可用性。
        if info.opened:
            return True
        if info.exit_type == "normal":
            return True
        if info.exit_type == "locked_key":
            return belief.keys > 0
        if info.exit_type == "conditional":
            if sym.monsters:
                return False
            unpressed = [button for button in sym.buttons if button not in belief.pressed_buttons]
            return not unpressed
        return belief.keys > 0 or not sym.chests

    def exit_value(self, sym: SymbolicObs, belief: BeliefState, info: ExitInfo) -> float:
        # 未尝试出口价值更高；刚进房间的返回门会被额外降权，鼓励探索新区域。
        sig = room_signature(sym)
        room = belief.rooms.get(sig)
        rec = room.exits.get(info.representative) if room is not None else None
        tried = bool(rec.tried) if rec is not None else False

        if info.exit_type == "locked_key":
            value = 95.0 if belief.keys > 0 else -999.0
        elif info.exit_type == "conditional":
            value = 45.0 if not tried else 18.0
        elif info.exit_type == "normal":
            value = 40.0 if not tried else 14.0
        elif info.opened:
            value = 80.0 if not tried else 24.0
        else:
            value = 20.0

        if self.looks_like_immediate_return(sym, belief, info):
            value -= 80.0
        return value

    def looks_like_immediate_return(
        self,
        sym: SymbolicObs,
        belief: BeliefState,
        info: ExitInfo,
    ) -> bool:
        if (
            belief.entry_return_direction is not None
            and info.direction == belief.entry_return_direction
            and len(sym.exit_infos) > 1
        ):
            return True
        if sym.player is None or belief.previous_room is None:
            return False
        if len(sym.exit_infos) <= 1:
            return False
        target = nearest_tile(sym.player, info.tiles)
        if target is None:
            return False
        if manhattan(sym.player, target) > 2:
            return False
        # 如果另一个可用出口还没探索，先不要马上从入口折返。
        for other in sym.exit_infos:
            if other is info or not self.exit_is_usable(sym, belief, other):
                continue
            other_target = nearest_tile(sym.player, other.tiles)
            if other_target is not None and manhattan(sym.player, other_target) > 2:
                return True
        return False
