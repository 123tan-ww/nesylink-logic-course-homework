from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

import numpy as np

from nesylink.core.constants import (
    ACTION_DOWN,
    ACTION_LEFT,
    ACTION_NOOP,
    ACTION_RIGHT,
    ACTION_UP,
)

TILE = 16
TILE_SIZE = 16

EMPTY = 0
WALL = 1
PLAYER = 2
MONSTER = 3
CHEST = 4
EXIT = 5
TRAP = 6
BUTTON = 7
NPC = 8
GAP = 9
BRIDGE = 10
SWITCH = 11
CHEST_OPENED = 12
UNKNOWN = 13

ROOM_W = 10
ROOM_H = 8

Pos = Tuple[int, int] # Tile position in the grid (x, y)
pxPos = Tuple[float, float]  # 像素坐标，表示地图区域内的左上角位置 (x, y)
RoomSig = Tuple[Tuple[int, ...], ...] # Room signature, a tuple of tuples representing the static structure of a room.

# ExitInfo dataclass, representing an exit in a room, including its tiles, direction, type, and other state information.
@dataclass
class ExitInfo:
    tiles: List[Pos]
    direction: str
    exit_type: str = "unknown"
    opened: bool = False
    score: float = 0.0

    # Optional topology fields kept for backward compatibility.
    dest: int = 0
    start: int = 0
    is_reached: bool = False

    @property
    def representative(self) -> Pos:
        return self.tiles[0] if self.tiles else (0, 0)

# 当前帧的符号观测：由像素识别得到，只描述当前房间里“看得见”的对象。
@dataclass
class SymbolicObs:
    grid: np.ndarray
    player: Optional[Pos] = None
    player_px: Optional[pxPos] = None
    facing: str = "down"
    monsters: List[Pos] = field(default_factory=list)
    monsters_px: List[pxPos] = field(default_factory=list)
    chests: List[Pos] = field(default_factory=list)
    exits: List[Pos] = field(default_factory=list)
    exit_infos: List[ExitInfo] = field(default_factory=list)  # 出口的方向、类型、是否打开等视觉信息
    exit_types: Dict[Pos, str] = field(default_factory=dict)
    exit_opened: Dict[Pos, bool] = field(default_factory=dict)
    traps: List[Pos] = field(default_factory=list)
    buttons: List[Pos] = field(default_factory=list)
    switches: List[Pos] = field(default_factory=list)


def room_signature(sym: SymbolicObs) -> RoomSig:
    """Stable room signature from visually observable static structure."""
    rows: List[Tuple[int, ...]] = []
    for y in range(ROOM_H):
        row: List[int] = []
        for x in range(ROOM_W):
            v = int(sym.grid[y, x])
            if v in {WALL, GAP, BRIDGE, EXIT, BUTTON, SWITCH, NPC}:
                row.append(v)
            else:
                # 玩家、怪物和宝箱会随时间变化，不能让它们把同一物理房间拆成多份记忆。
                row.append(EMPTY)
        rows.append(tuple(row))
    return tuple(rows)


# 记忆中的出口记录：除了视觉类型，还保存是否尝试过、是否连到上一房间。
@dataclass
class ExitRecord:
    tiles: List[Pos]
    direction: str
    exit_type: str = "unknown"
    opened: bool = False
    tried: bool = False
    leads_to: Optional[RoomSig] = None
    blocked: bool = False

# 每个房间一份长期记忆，用静态结构签名索引，避免跨房间混淆已开箱/已击杀状态。
@dataclass
class RoomMemory:
    sig: RoomSig
    seen_count: int = 0
    chests: Set[Pos] = field(default_factory=set)
    opened_chests: Set[Pos] = field(default_factory=set)
    monsters: Set[Pos] = field(default_factory=set)
    killed_monsters: Set[Pos] = field(default_factory=set)
    exits: Dict[Pos, ExitRecord] = field(default_factory=dict)
    has_locked_key_exit: bool = False

    @property
    def has_unopened_chest(self) -> bool:
        return any(chest not in self.opened_chests for chest in self.chests)

# Agent 的内部记忆：把视觉观测和历史反馈整合成可规划的状态。
@dataclass
class BeliefState:
    task_id: Optional[str] = None
    step: int = 0

    last_player: Optional[Pos] = None
    facing: str = "down"

    has_key: bool = False
    has_sword: bool = False
    keys: int = 0
    gold: int = 0
    items: Set[str] = field(default_factory=set)
    tools: Set[str] = field(default_factory=set)

    opened_chests: Set[Pos] = field(default_factory=set)
    killed_monsters: Set[Pos] = field(default_factory=set)
    pressed_buttons: Set[Pos] = field(default_factory=set)
    activated_switches: Set[Pos] = field(default_factory=set)
    blocked_exits: Set[Pos] = field(default_factory=set)
    switch_activations: int = 0
    topology_changed_since_room_change: bool = False

    rooms: Dict[RoomSig, RoomMemory] = field(default_factory=dict)
    current_room: Optional[RoomSig] = None
    previous_room: Optional[RoomSig] = None
    exit_attempt_room: Optional[RoomSig] = None
    exit_attempt_key: Optional[Pos] = None
    exit_attempt_direction: Optional[str] = None
    entry_return_direction: Optional[str] = None
    locked_key_room: Optional[RoomSig] = None

    last_action: int = ACTION_NOOP
    stuck_count: int = 0

    def reset(self, task_id: Optional[str] = None) -> None:
        self.task_id = task_id
        self.step = 0
        self.last_player = None
        self.facing = "down"
        self.has_key = False
        self.has_sword = False
        self.keys = 0
        self.gold = 0
        self.items.clear()
        self.tools.clear()
        self.opened_chests.clear()
        self.killed_monsters.clear()
        self.pressed_buttons.clear()
        self.activated_switches.clear()
        self.blocked_exits.clear()
        self.switch_activations = 0
        self.topology_changed_since_room_change = False
        self.rooms.clear()
        self.current_room = None
        self.previous_room = None
        self.exit_attempt_room = None
        self.exit_attempt_key = None
        self.exit_attempt_direction = None
        self.entry_return_direction = None
        self.locked_key_room = None
        self.last_action = ACTION_NOOP
        self.stuck_count = 0

    def update(self, sym: SymbolicObs, info=None) -> None:
        self.step += 1
        # 先更新物品栏和运动状态，再写入房间记忆；事件反馈最后处理，
        # 这样开箱/击杀会绑定到当前房间，而不是污染其它房间。
        self._update_inventory(info)
        self._update_motion(sym)
        self.update_room_memory(sym)
        self._update_events(sym, info)

    def _update_inventory(self, info=None) -> None:
        """从允许使用的物品栏信息更新钥匙、金币和装备状态。"""
        inv = info.get("inventory") if isinstance(info, dict) else None
        if not isinstance(inv, dict):
            return
        self.keys = int(inv.get("keys", 0))
        self.gold = int(inv.get("gold", 0))
        self.items = set(inv.get("items", []))
        self.tools = set(inv.get("tools", []))
        equipped = inv.get("equipped", {}) if isinstance(inv.get("equipped", {}), dict) else {}
        self.has_key = self.keys > 0
        self.has_sword = (
            "sword" in self.tools
            or "sword" in self.items
            or equipped.get("A") == "sword"
        )

    def _update_motion(self, sym: SymbolicObs) -> None:
        """ Update facing direction and stuck count based on player movement. """
        if self.last_player is not None and sym.player is not None:
            lx, ly = self.last_player
            x, y = sym.player
            if x > lx:
                self.facing = "right"
            elif x < lx:
                self.facing = "left"
            elif y > ly:
                self.facing = "down"
            elif y < ly:
                self.facing = "up"

            if (
                sym.player == self.last_player
                and self.last_action in {ACTION_UP, ACTION_DOWN, ACTION_LEFT, ACTION_RIGHT}
            ):
                self.stuck_count += 1
            else:
                self.stuck_count = 0

        self.last_player = sym.player
        sym.facing = self.facing

    def _update_events(self, sym: SymbolicObs, info=None) -> None:
        """用一步反馈修正历史记忆，例如记录刚打开的箱子或刚击杀的怪物。"""
        events = info.get("events", {}) if isinstance(info, dict) else {}
        flags = events.get("flags", {}) if isinstance(events, dict) else {}

        if flags.get("chest_opened", False) and sym.player is not None:
            chest_pos = self._front_tile(sym.player, self.facing)
            if chest_pos is not None:
                self.opened_chests.add(chest_pos)
                room = self.rooms.get(self.current_room) if self.current_room is not None else None
                if room is not None:
                    room.chests.add(chest_pos)
                    room.opened_chests.add(chest_pos)

        if flags.get("monster_killed", False):
            monster_pos = self._front_tile(sym.player, self.facing) if sym.player is not None else None
            if monster_pos is not None:
                self.killed_monsters.add(monster_pos)
                room = self.rooms.get(self.current_room) if self.current_room is not None else None
                if room is not None:
                    room.killed_monsters.add(monster_pos)

        if flags.get("button_pressed", False) and sym.player is not None:
            self.pressed_buttons.add(sym.player)

        if flags.get("switch_activated", False):
            self.switch_activations += 1
            if sym.player is not None:
                switch_pos = self._front_tile(sym.player, self.facing)
                if switch_pos is not None:
                    self.activated_switches.add(switch_pos)
                self.activated_switches.add(sym.player)
            self.topology_changed_since_room_change = True

        if flags.get("room_changed", False):
            if self.exit_attempt_direction is not None:
                self.entry_return_direction = self._opposite_direction(self.exit_attempt_direction)
            self.activated_switches.clear()
            self.topology_changed_since_room_change = False

    def update_facing_from_action(self, action: int) -> None:
        """移动动作会改变朝向，攻击/防御不会。"""
        if action == ACTION_UP:
            self.facing = "up"
        elif action == ACTION_DOWN:
            self.facing = "down"
        elif action == ACTION_LEFT:
            self.facing = "left"
        elif action == ACTION_RIGHT:
            self.facing = "right"

    def update_room_memory(self, sym: SymbolicObs) -> None:
        """把当前视觉状态合并进房间记忆，并维护出口拓扑。"""
        observed_sig = room_signature(sym)
        entered_from_room: Optional[RoomSig] = None
        reverse_exit_direction: Optional[str] = None
        has_exit_attempt = (
            self.exit_attempt_room is not None
            and self.exit_attempt_key is not None
        )

        if self.current_room is None:
            self.current_room = observed_sig
        elif self.current_room != observed_sig and has_exit_attempt:
            self.previous_room = self.current_room
            entered_from_room = self.current_room
            self.current_room = observed_sig

        sig = self.current_room

        if (
            entered_from_room is not None
            and self.exit_attempt_room is not None
            and self.exit_attempt_key is not None
        ):
            src_room = self.rooms.get(self.exit_attempt_room)
            rec = self._find_exit_record(src_room, self.exit_attempt_key) if src_room is not None else None
            if rec is not None:
                rec.tried = True
                rec.leads_to = sig
                reverse_exit_direction = self._opposite_direction(rec.direction)
            elif self.exit_attempt_direction is not None:
                reverse_exit_direction = self._opposite_direction(self.exit_attempt_direction)
            self.exit_attempt_room = None
            self.exit_attempt_key = None
            self.exit_attempt_direction = None

        room = self.rooms.setdefault(sig, RoomMemory(sig=sig))
        room.seen_count += 1

        for chest in sym.chests:
            if chest not in room.opened_chests:
                room.chests.add(chest)

        room.monsters = set(sym.monsters)

        for info in sym.exit_infos:
            key = info.representative
            old = room.exits.get(key)
            room.exits[key] = ExitRecord(
                tiles=list(info.tiles),
                direction=info.direction,
                exit_type=info.exit_type,
                opened=info.opened,
                tried=old.tried if old else False,
                leads_to=old.leads_to if old else None,
                blocked=old.blocked if old else False,
            )
            if info.exit_type == "locked_key":
                room.has_locked_key_exit = True
                self.locked_key_room = sig

        if entered_from_room is not None:
            entry_exit_direction = reverse_exit_direction
            if entry_exit_direction is None and sym.player is not None:
                entry_exit_direction = self._reverse_exit_direction_from_spawn(sym.player)
            if entry_exit_direction is not None:
                for rec in room.exits.values():
                    if rec.direction == entry_exit_direction:
                        rec.tried = True
                        rec.leads_to = entered_from_room
                        break

    def _front_tile(self, pos: Pos, facing: str) -> Optional[Pos]:
        """ Get the tile position in front of the player based on their current position and facing direction. """
        x, y = pos
        if facing == "up":
            return (x, y - 1)
        if facing == "down":
            return (x, y + 1)
        if facing == "left":
            return (x - 1, y)
        if facing == "right":
            return (x + 1, y)
        return None

    def _reverse_exit_direction_from_spawn(self, pos: Pos) -> Optional[str]:
        """ Determine the exit direction based on the player's spawn position within the room. """
        x, y = pos
        if x <= 1:
            return "west"
        if x >= ROOM_W - 2:
            return "east"
        if y <= 1:
            return "north"
        if y >= ROOM_H - 2:
            return "south"
        return None

    def _find_exit_record(self, room: Optional[RoomMemory], tile: Pos) -> Optional[ExitRecord]:
        """ Find the exit record in the given room that corresponds to the specified tile position. """
        if room is None:
            return None
        direct = room.exits.get(tile)
        if direct is not None:
            return direct
        for rec in room.exits.values():
            if tile in rec.tiles:
                return rec
        return None

    def _opposite_direction(self, direction: str) -> Optional[str]:
        """ Get the opposite direction of the given direction string. """
        if direction == "north":
            return "south"
        if direction == "south":
            return "north"
        if direction == "west":
            return "east"
        if direction == "east":
            return "west"
        return None

# 规划器内部使用的子目标和候选目标记录。
@dataclass
class Subgoal:
    kind: str
    target: Optional[Pos] = None
    facing: Optional[int] = None
    dest_room_id: Optional[int] = None
    start_room_id: Optional[int] = None
    exit_dir: Optional[str] = None


@dataclass
class Candidate:
    subgoal: Subgoal
    value: float
    dist: float
    risk: float
    score: float
