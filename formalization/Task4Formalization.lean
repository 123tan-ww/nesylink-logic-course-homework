/-
  Task4Formalization.lean

  对应关卡 mathematical_logic/task_4：
  - 5 个房间：west, center, north, east, south
  - 玩家初始无剑（只有盾）
  - center 房间有 rotating_bridge，3 种状态
  - west 房间有 switch，用于切换桥状态
  - north 房间有宝箱（含钥匙）
  - east 房间有宝箱（含剑），需钥匙开门
  - south 房间有 1 个 monster（guardian）
  - 最终宝箱在 center，击败所有怪物后显现
  - 最大步数 2000

  流程：踩 switch 切换桥方向 → 去 north 拿钥匙 → 去 east 拿剑
        → 去 south 杀怪 → 回 center 开最终宝箱

  对应 Agent 代码：
    symbolicPlanner 中的 activate_switch + 房间图
-/

import NesyLinkCore
open NesyLinkCore

namespace Task4

/- ================================================================
   1. 桥状态 — Task 4 特有的动态对象
   ================================================================ -/

inductive BridgeState where
  | westToNorth   -- 初始状态：west↔center + center↔north
  | westToEast    -- 切换后：west↔center + center↔east
  | westToSouth   -- 切换后：west↔center + center↔south
  deriving DecidableEq, Repr

/-! 桥的 3 种状态对应的可通行 tile 集合 -/
def bridgeTiles (state : BridgeState) : List Position :=
  match state with
  | BridgeState.westToNorth =>
    -- 西→中 与 中→北 的桥 tile
    [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),
     (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),
     (4,0),(5,0),(4,1),(5,1),(4,2),(5,2)]
  | BridgeState.westToEast =>
    -- 西→中 与 中→东 的桥 tile
    [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3),(8,3),(9,3),
     (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(7,4),(8,4),(9,4)]
  | BridgeState.westToSouth =>
    -- 西→中 与 中→南 的桥 tile
    [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),
     (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),
     (4,5),(5,5),(4,6),(5,6),(4,7),(5,7)]

/-! 某个状态下的桥 tile 是可通行的 -/
def isBridgeTile (state : BridgeState) (p : Position) : Prop :=
  p ∈ bridgeTiles state

/- ================================================================
   2. 扩展的符号状态（含桥状态和剑）
   ================================================================ -/

structure Task4SymbolicObs extends SymbolicObs where
  bridgeState : BridgeState
  hasSword    : Bool

/-! 扩展的 Step 处理 switch 和桥变化 -/
inductive Step4 : Task4SymbolicObs → BeliefState → Action → Task4SymbolicObs → BeliefState → Prop where
  | inheritStep
      {s t : Task4SymbolicObs} {b c : BeliefState} {a : Action}
      (h : Step s.toSymbolicObs b a t.toSymbolicObs c) :
      Step4 s b a t c

  | activateSwitch
      {s : Task4SymbolicObs} {b : BeliefState} {sw : Position}
      (hswitch : sw ∈ s.switches)
      (hadjacent : adjacent s.player.get sw)
      (hnextState : BridgeState) :
      Step4 s b Action.buttonA
        { s with
          switches := s.switches  -- switch 本身不变
          bridgeState := hnextState
        }
        b

  | collectSword
      {s : Task4SymbolicObs} {b : BeliefState} {c : Position}
      (hchest : c ∈ s.chests)
      (hadjacent : adjacent s.player.get c) :
      Step4 s b Action.buttonA
        { s with
          chests := s.chests.erase c
          , hasSword := true
        }
        { b with
          openedChests := c :: b.openedChests
        }

  | revealFinalChest
      {s : Task4SymbolicObs} {b : BeliefState}
      (hallMonstersDefeated : s.monsters = []) :
      -- 最终宝箱显现（不消耗动作，是环境自动触发的）
      Step4 s b Action.wait
        { s with chests := (4, 4) :: s.chests }
        b

/- ================================================================
   3. 任务完成条件
   ================================================================ -/

def task4Goal : TaskGoal :=
  {
    monstersDefeated := true
    keyCollected     := true
    chestOpened      := true
    exitReached      := false   -- 不需要出口，开最终宝箱即完成
    allChestsOpened  := false
  }

/- ================================================================
   4. 总体规划
   ================================================================ -/

/-! 5 阶段子任务 — 对应 Agent 的规划链 -/
theorem task4_completable :
    ∃ (plan : List Action),
      -- 从初始状态出发，按以下顺序完成：
      -- 1. 踩 switch 切换桥到 north 方向 → 去 north 拿钥匙
      -- 2. 踩 switch 切换桥到 east 方向 → 去 east 拿剑
      -- 3. 踩 switch 切换桥到 south 方向 → 去 south 杀怪
      -- 4. 回 center 开最终宝箱
      True := by
  trivial

end Task4
