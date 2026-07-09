/-
  Task2Formalization.lean

  对应关卡 mathematical_logic/task_2：
  - 单房间，无墙障碍
  - 玩家起点 (7, 3)
  - 怪物 chaser 在 (2, 2)，HP 2
  - 宝箱在 (1, 3)，内含钥匙
  - 西侧条件门（需要击杀怪物 + 持有钥匙）
  - 上下两行有陷阱
  - 最大步数 500

  对应 Agent 代码中的子目标链：
    killMonster → findChest → goExit
-/

import NesyLinkCore
open NesyLinkCore

namespace Task2

/- ================================================================
   1. 地图常量
   ================================================================ -/

def MONSTER_POS : Position := (2, 2)
def CHEST_POS  : Position := (1, 3)
def EXIT_POSITIONS : List Position := [(0, 3), (0, 4)]

def TRAP_POSITIONS : List Position := [
  (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0),
  (1, 7), (2, 7), (3, 7), (4, 7), (5, 7), (6, 7), (7, 7), (8, 7)
]

def INIT_PLAYER : Position := (7, 3)

/- ================================================================
   2. Grid 构造
   ================================================================ -/

def buildTask2Grid : Grid :=
  List.range ROOM_H |>.map (λ y =>
    List.range ROOM_W |>.map (λ x =>
      if (x, y) ∈ TRAP_POSITIONS then TILE_TRAP
      else if (x, y) = MONSTER_POS then TILE_MONSTER
      else if (x, y) = CHEST_POS then TILE_CHEST
      else TILE_EMPTY
    )
  )

/- ================================================================
   3. 初始状态
   ================================================================ -/

def initSym : SymbolicObs :=
  {
    player    := some INIT_PLAYER
    facing    := Direction.down
    monsters  := [MONSTER_POS]
    chests    := [CHEST_POS]
    exits     := EXIT_POSITIONS
    traps     := TRAP_POSITIONS
    buttons   := []
    switches  := []
    grid      := buildTask2Grid
  }

def initBelief : BeliefState :=
  {
    hasKey      := false
    hasSword    := true
    keys        := 0
    gold        := 0
    openedChests  := []
    killedMonsters := []
    pressedButtons := []
    step        := 0
  }

def task2Goal : TaskGoal :=
  {
    monstersDefeated := true
    keyCollected     := true
    chestOpened      := true
    exitReached      := true
    allChestsOpened  := false
  }

/- ================================================================
   4. 陷阱不可通行
   ================================================================ -/

theorem traps_are_blocked (p : Position) (ht : p ∈ TRAP_POSITIONS) :
    isBlocked buildTask2Grid p := by
  unfold isBlocked getTile buildTask2Grid
  sorry

/- ================================================================
   5. 三段式子目标组合可达性
   ================================================================ -/

/-! 阶段 1：走向怪物并攻击 -/
theorem phase1_kill_monster :
    ∃ (plan : List Action) (midSym : SymbolicObs) (midBelief : BeliefState),
      Exec initSym initBelief plan midSym midBelief ∧
      MONSTER_POS ∉ midSym.monsters := by
  -- 路径: left×4 → up×1（走到怪物相邻格）→ 攻击
  -- 对应 Agent 的 killMonster 子目标
  sorry

/-! 阶段 2：走向宝箱并开箱 -/
theorem phase2_open_chest
    (midSym : SymbolicObs) (midBelief : BeliefState)
    (hkilled : midSym.monsters = []) :
    ∃ (plan : List Action) (midSym2 : SymbolicObs) (midBelief2 : BeliefState),
      Exec midSym midBelief plan midSym2 midBelief2 ∧
      CHEST_POS ∈ midBelief2.openedChests := by
  -- 路径: left×2（走到宝箱相邻格）→ 按 A 开箱
  -- 对应 Agent 的 findChest 子目标
  sorry

/-! 阶段 3：走向出口 -/
theorem phase3_reach_exit
    (midSym2 : SymbolicObs) (midBelief2 : BeliefState)
    (hhasKey : midBelief2.hasKey) :
    ∃ (plan : List Action) (finalSym : SymbolicObs) (finalBelief : BeliefState),
      Exec midSym2 midBelief2 plan finalSym finalBelief ∧
      finalSym.player.get ∈ EXIT_POSITIONS := by
  -- 路径: left×1 → down×1（走到出口位置）
  -- 对应 Agent 的 goExit 子目标
  sorry

/-! 三阶段组合 → 任务整体可达 -/
theorem task2_completable :
    TaskCompletable initSym initBelief task2Goal := by
  rcases phase1_kill_monster with ⟨plan1, midSym, midBelief, hexec1, hkilled⟩
  rcases phase2_open_chest midSym midBelief hkilled with ⟨plan2, midSym2, midBelief2, hexec2, hopened⟩
  rcases phase3_reach_exit midSym2 midBelief2 (by
    -- 从 midBelief2 中可推出 hasKey = true
    sorry
  ) with ⟨plan3, finalSym, finalBelief, hexec3, hatexit⟩

  -- 用 Exec 的组合性拼接三段计划
  -- plan = plan1 ++ plan2 ++ plan3
  sorry

end Task2
