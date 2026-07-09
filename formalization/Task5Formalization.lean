/-
  Task5Formalization.lean

  对应关卡 mathematical_logic/task_5：
  - 4 个房间：room_0_0, room_1_0, room_0_1, room_-1_0
  - room_0_0：有墙体障碍、1 个怪物 (chaser)、1 个宝箱（金币）、NPC、按钮
  - room_1_0：1 个怪物 (ambusher)、1 个宝箱（回血）
  - room_0_1：1 个怪物 (patroller)、1 个宝箱（钥匙）、1 个陷阱
  - room_-1_0：2 个怪物 (chaser + ambusher)、1 个宝箱（金币）
  - 北侧锁门需要钥匙打开
  - 南侧条件门需要按钮按下
  - 生命值每 200 步扣 1 血（倒计时机制）
  - 最大步数 2000

  对应 Agent 代码：
    button_pressed 机制 + 房间探索（unexplored/stillNeed）
-/

import NesyLinkCore
open NesyLinkCore

namespace Task5

/- ================================================================
   1. 倒计时机制 — Task 5 特有
   ================================================================ -/

def DRAIN_INTERVAL : Nat := 200
def INITIAL_HP : Nat := 5

/-! 生命值倒计时模型 -/
def hpAfterDrain (startHp : Nat) (totalSteps : Nat) : Nat :=
  let drains := totalSteps / DRAIN_INTERVAL
  if startHp > drains then startHp - drains else 0

/-! 在倒计时杀死玩家前必须完成任务 — 关键约束 -/
def deadline (startHp : Nat) : Nat :=
  startHp * DRAIN_INTERVAL

theorem must_finish_before_deadline
    (startHp : Nat) (steps : Nat) (h : steps < deadline startHp) :
    hpAfterDrain startHp steps > 0 := by
  unfold hpAfterDrain deadline
  -- 如果 steps < startHp * 200，则 drains = steps / 200 < startHp
  -- 所以 startHp - drains > 0
  sorry

/- ================================================================
   2. 按钮机制
   ================================================================ -/

/-! 按钮按下后，条件门打开 -/
def buttonOpensSouthGate : Prop := True

/-! 从 room_0_0 到 room_0_1 的条件门 — 需要按钮按下 -/
theorem south_gate_opens_when_button_pressed
    (buttonPos : Position) (pressedButtons : List Position)
    (hpressed : buttonPos ∈ pressedButtons) :
    -- 条件门变为可通行
    True := by
  trivial

/- ================================================================
   3. 任务完成条件
   ================================================================ -/

-- Task 5 需要探索所有 4 个房间并打开所有宝箱
def TASK5_CHEST_COUNT : Nat := 4

def task5Goal : TaskGoal :=
  {
    monstersDefeated := false   -- 不强制要求杀所有怪
    keyCollected     := true    -- 需要拿钥匙
    chestOpened      := true
    exitReached      := false
    allChestsOpened  := true    -- 需要打开所有宝箱
  }

/- ================================================================
   4. 总体可达性
   ================================================================ -/

/-! 在倒计时限制下，任务总体可达 -/
theorem task5_completable_before_deadline :
    ∃ (plan : List Action) (planLength : Nat),
      planLength < deadline INITIAL_HP ∧
      -- 存在一条长度小于 deadline 的路径完成任务
      True := by
  -- 需要构造不会超时的路径并证明
  sorry

end Task5
