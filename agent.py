from __future__ import annotations

from collections import deque
from typing import Deque, Optional

from nesylink.core.constants import (
    ACTION_A,
    ACTION_B,
    ACTION_DOWN,
    ACTION_LEFT,
    ACTION_NOOP,
    ACTION_RIGHT,
    ACTION_UP,
)

from Dataclass import ROOM_H, ROOM_W, TILE_SIZE, BeliefState, Pos, Subgoal, SymbolicObs
from optionController import action_to_face, action_to_name, get_exit_info_for_tile
from optionController import exit_approach_tiles
from optionController import exit_out_action
from safetyShield import SafetyShield
from symbolicPlanner import MOVE_ACTIONS, manhattan
from symbolicPlanner import SymbolicPlanner
from optionController import OptionController
from vision_exact import PixelPerception


class Policy:
    def __init__(self) -> None:
        # 四层结构：像素感知 -> 信念记忆 -> 符号规划 -> 动作执行/安全过滤。
        self.perception = PixelPerception()
        self.belief = BeliefState()
        self.planner = SymbolicPlanner()
        self.controller = OptionController()
        self.shield = SafetyShield()

        self.action_queue: Deque[int] = deque()
        self.current_subgoal: Optional[Subgoal] = None
        self.last_sym: Optional[SymbolicObs] = None
        self.last_action = ACTION_NOOP
        self.perception_interval = 40
        # 出口需要连续按住方向直到真正换房；期间若收到换房反馈就停止强制前进。
        self.force_exit_action: Optional[int] = None
        self.force_exit_steps = 0
        # 近身战状态：未面向怪物时先举盾，再转向；像素贴近但未对齐时短暂防御。
        self.guarded_face_action: Optional[int] = None
        self.pixel_guard_cooldown = 0

    def reset(self, seed: int | None = None, task_id: str | None = None) -> None:
        del seed
        self.belief.reset(task_id=task_id)
        self.action_queue.clear()
        self.current_subgoal = None
        self.last_sym = None
        self.last_action = ACTION_NOOP
        self.force_exit_action = None
        self.force_exit_steps = 0
        self.guarded_face_action = None
        self.pixel_guard_cooldown = 0

    def act(self, obs, info=None) -> int:
        if self.pixel_guard_cooldown > 0:
            self.pixel_guard_cooldown -= 1

        # 正在穿过出口时优先执行出口动作，避免重规划把角色停在门口。
        if self.force_exit_steps > 0 and self.force_exit_action is not None:
            if self.info_has_any_event(info, {"room_changed", "exit_reached", "world_completed"}):
                self.force_exit_action = None
                self.force_exit_steps = 0
                self.action_queue.clear()
                self.last_sym = None
            else:
                self.force_exit_steps -= 1
                self.belief.step += 1
                self.belief.update_facing_from_action(self.force_exit_action)
                self.last_action = self.force_exit_action
                return int(self.force_exit_action)

        need_vision = (
            self.last_sym is None
            or not self.action_queue
            or self.belief.step % self.perception_interval == 0
            or self.info_has_replan_event(info)
        )

        if need_vision:
            # 重新从像素帧抽象符号状态，修正移动怪物和动态机关带来的误差。
            sym = self.perception(obs)
            self.last_sym = sym
            self.belief.update(sym, info)
        else:
            # 队列执行中用上一帧的像素位置做轻量预测，减少每步模板匹配开销。
            self.update_sym_from_action(self.last_action)
            sym = self.last_sym
            self.belief.step += 1

        # if self.belief.step % 10 == 0:
        #     save_training_frame(obs, self.belief.step, 5)

        self.mark_obvious_subgoal_progress(sym)

        if self.need_replan(sym, info):
            self.current_subgoal = self.planner.next_subgoal(sym, self.belief)
            actions = self.controller.build_actions(sym, self.belief, self.current_subgoal)
            self.action_queue = deque(actions)

        raw_action = self.action_queue.popleft() if self.action_queue else ACTION_NOOP

        # 宝箱/开关在环境里只要求相邻，不要求面向；相邻后立即交互可节省时间。
        interact_action = self.interactable_action_override(sym)
        if interact_action is not None:
            self.belief.last_action = interact_action
            self.last_action = interact_action
            return int(interact_action)

        # 怪物近身时覆盖队列动作，防止过期路径把“转向”误执行成撞向怪物。
        combat_action = self.combat_action_override(sym, raw_action)
        if combat_action is not None:
            self.belief.update_facing_from_action(combat_action)
            self.belief.last_action = combat_action
            self.last_action = combat_action
            return int(combat_action)

        required_exit_action = self.exit_action_if_on_current_exit(sym)
        if (
            self.current_subgoal is not None
            and self.current_subgoal.kind == "go_exit"
            and required_exit_action is not None
        ):
            raw_action = required_exit_action
            self.force_exit_action = required_exit_action
            self.force_exit_steps = 40
            self.action_queue.clear()
            if self.belief.current_room is not None:
                exit_info = None
                if self.current_subgoal.target is not None:
                    exit_info = get_exit_info_for_tile(sym, self.current_subgoal.target)
                self.belief.exit_attempt_room = self.belief.current_room
                self.belief.exit_attempt_key = self.current_subgoal.target
                self.belief.exit_attempt_direction = exit_info.direction if exit_info is not None else None
            self.belief.update_facing_from_action(raw_action)
            self.belief.last_action = raw_action
            self.last_action = raw_action
            return int(raw_action)

        safe_action, consume_raw = self.shield.filter(raw_action, sym, self.belief)
        if not consume_raw:
            self.action_queue.appendleft(raw_action)
            self.last_sym = None

        self.belief.update_facing_from_action(safe_action)
        self.belief.last_action = safe_action
        self.last_action = safe_action
        return int(safe_action)

    def need_replan(self, sym: SymbolicObs, info=None) -> bool:
        # 子目标完成、目标消失、卡住或发生关键反馈时重规划。
        if sym.player is None:
            self.action_queue.clear()
            return True
        if not self.action_queue:
            return True
        if self.info_has_replan_event(info):
            self.action_queue.clear()
            return True
        if self.belief.stuck_count >= 8:
            self.action_queue.clear()
            return True
        if self.current_subgoal is not None:
            target = self.current_subgoal.target
            if self.current_subgoal.kind == "find_chest" and target not in sym.chests:
                self.action_queue.clear()
                return True
            if self.current_subgoal.kind == "attack_monster" and target not in sym.monsters:
                self.action_queue.clear()
                return True
        return False

    def info_has_replan_event(self, info=None) -> bool:
        if not isinstance(info, dict):
            return False
        events = info.get("events", {})
        if not isinstance(events, dict):
            return False
        flags = events.get("flags", {}) or {}
        important = {
            "chest_opened",
            "key_collected",
            "gold_collected",
            "item_collected",
            "agent_healed",
            "monster_damaged",
            "monster_killed",
            "door_opened",
            "button_pressed",
            "switch_activated",
            "bridge_rotated",
            "dynamic_object_state_changed",
            "room_changed",
            "exit_reached",
            "trap_triggered",
            "world_completed",
        }
        return any(bool(flags.get(name, False)) for name in important)
    
    # def info_has_replan_reward(self, info=None)->bool:
    #     if not isinstance(info, dict):
    #         return False
    #     reward = info.get

    def info_has_any_event(self, info, names: set[str]) -> bool:
        if not isinstance(info, dict):
            return False
        events = info.get("events", {})
        if not isinstance(events, dict):
            return False
        flags = events.get("flags", {}) or {}
        return any(bool(flags.get(name, False)) for name in names)

    def mark_obvious_subgoal_progress(self, sym: SymbolicObs) -> None:
        if self.current_subgoal is None or sym.player is None:
            return
        if self.current_subgoal.kind == "press_button" and sym.player == self.current_subgoal.target:
            self.belief.pressed_buttons.add(sym.player)

    def interactable_action_override(self, sym: SymbolicObs) -> Optional[int]:
        # A 键优先交互相邻的宝箱/开关；这里直接消耗队列，避免继续做多余对齐。
        if (
            sym.player is None
            or self.current_subgoal is None
            or self.current_subgoal.kind not in {"find_chest", "activate_switch"}
            or self.current_subgoal.target is None
        ):
            return None
        if manhattan(sym.player, self.current_subgoal.target) != 1:
            return None
        self.action_queue.clear()
        return ACTION_A

    def update_sym_from_action(self, action: int) -> None:
        # 简单的像素运动模型：每个移动动作预测 1px，用中心点映射回 tile。
        sym = self.last_sym
        if sym is None or sym.player_px is None or sym.player is None:
            return
        if action not in MOVE_ACTIONS:
            return

        dx, dy = 0.0, 0.0
        if action == ACTION_LEFT:
            dx = -1.0
            sym.facing = "left"
        elif action == ACTION_RIGHT:
            dx = 1.0
            sym.facing = "right"
        elif action == ACTION_UP:
            dy = -1.0
            sym.facing = "up"
        elif action == ACTION_DOWN:
            dy = 1.0
            sym.facing = "down"

        x, y = sym.player_px
        x = max(0.0, min(float((ROOM_W - 1) * TILE_SIZE), x + dx))
        y = max(0.0, min(float((ROOM_H - 1) * TILE_SIZE), y + dy))
        sym.player_px = (x, y)
        tx = int(max(0, min(ROOM_W - 1, (x + TILE_SIZE * 0.5) // TILE_SIZE)))
        ty = int(max(0, min(ROOM_H - 1, (y + TILE_SIZE * 0.5) // TILE_SIZE)))
        sym.player = (tx, ty)
        self.belief.update_facing_from_action(action)
        sym.facing = self.belief.facing

    def combat_action_override(self, sym: SymbolicObs, action: int) -> Optional[int]:
        # 通用近身战规则：
        # 1. 相邻且已面向怪物 -> 直接攻击。
        # 2. 相邻但未面向 -> 先举盾，再转向/攻击。
        # 3. 像素距离很近但斜向未对齐 -> 带冷却举盾保命。
        if (
            sym.player is None
            or self.current_subgoal is None
            or self.current_subgoal.kind != "attack_monster"
        ):
            self.guarded_face_action = None
            return None

        face_action = self.adjacent_monster_face_action(sym)
        if face_action is not None:
            desired_facing = action_to_name(face_action)
            already_facing = self.belief.facing == desired_facing or sym.facing == desired_facing

            if already_facing:
                if action != ACTION_A:
                    self.action_queue.clear()
                self.guarded_face_action = None
                return ACTION_A

            if action == face_action:
                if self.last_action == ACTION_B or self.guarded_face_action == face_action:
                    self.guarded_face_action = None
                    return face_action
                self.guarded_face_action = face_action
                self.action_queue.appendleft(action)
                return ACTION_B

            if action == ACTION_A:
                if self.last_action == ACTION_B:
                    self.action_queue.appendleft(ACTION_A)
                    return face_action
                self.guarded_face_action = face_action
                self.action_queue.appendleft(ACTION_A)
                self.action_queue.appendleft(face_action)
                return ACTION_B

            return None

        self.guarded_face_action = None
        if (
            action in MOVE_ACTIONS
            and self.pixel_guard_cooldown == 0
            and self.last_action != ACTION_B
            and self.pixel_close_unaligned_monster(sym)
        ):
            self.pixel_guard_cooldown = 6
            self.action_queue.appendleft(action)
            return ACTION_B

        return None

    def adjacent_monster_face_action(self, sym: SymbolicObs) -> Optional[int]:
        # 返回当前相邻怪物所在方向；优先使用视觉中的真实相邻怪物。
        if (
            sym.player is None
            or self.current_subgoal is None
            or self.current_subgoal.kind != "attack_monster"
        ):
            return None
        for monster in sym.monsters:
            if manhattan(sym.player, monster) == 1:
                return action_to_face(sym.player, monster)
        target = self.current_subgoal.target
        if target is not None and manhattan(sym.player, target) == 1:
            return action_to_face(sym.player, target)
        return None

    def pixel_close_unaligned_monster(self, sym: SymbolicObs) -> bool:
        # tile 还没相邻时，像素 AABB 可能已经接近接触；此时短暂举盾更稳。
        if sym.player_px is None or not sym.monsters_px:
            return False
        px, py = sym.player_px
        for mx, my in sym.monsters_px:
            dx = abs(mx - px)
            dy = abs(my - py)
            close = dx <= TILE_SIZE * 1.25 and dy <= TILE_SIZE * 1.25
            aligned = dx <= 4.0 or dy <= 4.0
            if close and not aligned:
                return True
        return False

    def exit_action_if_on_current_exit(self, sym: SymbolicObs) -> Optional[int]:
        # 玩家位于出口或出口内侧邻接格时，直接持续朝出口方向移动。
        if sym.player is None or self.current_subgoal is None or self.current_subgoal.kind != "go_exit":
            return None
        target = self.current_subgoal.target
        if target is None:
            return None
        info = get_exit_info_for_tile(sym, target)
        if info is None:
            return None

        valid_tiles = set(info.tiles) | set(exit_approach_tiles(info))
        if sym.player in valid_tiles:
            return exit_out_action(info)
        return None


def make_policy() -> Policy:
    return Policy()

from pathlib import Path
from PIL import Image
import numpy as np


def save_training_frame(obs, step: int, task_id:int = 1, seed: int = 0) -> None:
    output_dir = Path("dataset/frames") / f"seed_{seed}" / f"task{task_id}"
    output_dir.mkdir(parents=True, exist_ok=True)

    frame = np.asarray(obs)[:128, :160, :3].astype(np.uint8)

    Image.fromarray(frame).save(
        output_dir / f"frame_{step:06d}.png"
    )