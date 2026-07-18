/-
  Task1Formalization.lean - mathematical_logic/task_1

  对应关卡 mathematical_logic/task_1 的形式化：
  - 单房间（10×8 tile grid）
  - 玩家起点 (4, 6)
  - 宝箱在 (0, 3)，内含钥匙
  - 北侧锁门在 (4, 0) / (5, 0)
  - 墙体障碍：y=2 行（列 0-1、4-9）和 y=5 行（列 0-6）
  - 最简路径：右绕到右上角 → 上绕到宝箱行 → 左走到宝箱 → 开箱 → 右移到中部 → 上到北出口 → 出门

  对应 Agent 代码中的子目标链：
    findChest → goExit
-/

import NesyLinkCore
open NesyLinkCore
namespace Task1

/- ================================================================
   1. 地图常量
   ================================================================ -/

def WALLS : List Position :=
  [(0,2),(1,2),(4,2),(5,2),(6,2),(7,2),(8,2),(9,2),
   (0,5),(1,5),(2,5),(3,5),(4,5),(5,5),(6,5)]

def CHEST_POS : Position := (0, 3)
def EXIT_POSITIONS : List Position := [(4, 0), (5, 0)]
def INIT_PLAYER : Position := (4, 6)

/- ================================================================
   2. Grid 构造
   ================================================================ -/

def buildTask1Grid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ WALLS then TILE_WALL else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

/- ================================================================
   3. 初始状态与任务目标
   ================================================================ -/

def initSym : SymbolicObs :=
  { player := some INIT_PLAYER, facing := Direction.down, monsters := [],
    chests := [CHEST_POS], exits := EXIT_POSITIONS, traps := [],
    buttons := [], switches := [], grid := buildTask1Grid }

def initBelief : BeliefState :=
  { hasKey := false, hasSword := true, keys := 0, gold := 0,
    openedChests := [], killedMonsters := [], pressedButtons := [], step := 0 }

def task1Goal : TaskGoal :=
  { monstersDefeated := false, keyCollected := true, chestOpened := true,
    exitReached := true, allChestsOpened := false }

/- ================================================================
   4. 路径安全性 — 枚举运行路径上所有需要验证安全的位置
   ================================================================ -/

/-- 本关规划路径经过的所有 tile 位置（非墙、可通行） -/
def pathPositions : List Position := [
  -- Phase 1: start → chest
  (5,6), (6,6), (7,6), (7,5), (7,4), (7,3),
  (6,3), (5,3), (4,3), (3,3), (2,3), (1,3),
  -- Phase 3: chest → exit
  (2,3), (3,3), (3,2), (3,1), (3,0), (4,0)
]

/-- 路径上的所有位置都是安全的（在 bounds 内且不是墙/陷阱/gap）
    直接展开所有定义为原语后用 native_decide 一次性验证。 -/
theorem pathPositions_safe : ∀ p ∈ pathPositions, isSafeMove buildTask1Grid p := by
  simp [pathPositions, isSafeMove, isBlocked, inBounds, getTile, buildTask1Grid, WALLS, ROOM_H, ROOM_W, TILE_EMPTY, TILE_WALL, TILE_TRAP, TILE_GAP]
  all_goals { native_decide }

/- ================================================================
   5. 单步移动引理
   ================================================================ -/

theorem step_right (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildTask1Grid) (hp : s.player = some (x, y))
    (hsafe : (x+1, y) ∈ pathPositions) :
    Step s b Action.right { s with player := some (x+1, y), facing := Direction.right } { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.right) := by
    simpa [hg, hp, nextPosition] using pathPositions_safe (x+1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_up (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildTask1Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y-1) ∈ pathPositions) :
    Step s b Action.up { s with player := some (x, y-1), facing := Direction.up } { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.up) := by
    simpa [hg, hp, nextPosition] using pathPositions_safe (x, y-1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_left (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildTask1Grid) (hp : s.player = some (x, y))
    (hsafe : (x-1, y) ∈ pathPositions) :
    Step s b Action.left { s with player := some (x-1, y), facing := Direction.left } { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.left) := by
    simpa [hg, hp, nextPosition] using pathPositions_safe (x-1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

/- ================================================================
   6. 中间状态定义
   ================================================================ -/

-- Phase 1: 从起点 (4,6) 到宝箱旁 (1,3)
def s_R1 : SymbolicObs := { initSym with player := some (5, 6), facing := Direction.right }
def s_R2 : SymbolicObs := { initSym with player := some (6, 6), facing := Direction.right }
def s_R3 : SymbolicObs := { initSym with player := some (7, 6), facing := Direction.right }
def s_U1 : SymbolicObs := { initSym with player := some (7, 5), facing := Direction.up }
def s_U2 : SymbolicObs := { initSym with player := some (7, 4), facing := Direction.up }
def s_U3 : SymbolicObs := { initSym with player := some (7, 3), facing := Direction.up }
def s_L1 : SymbolicObs := { initSym with player := some (6, 3), facing := Direction.left }
def s_L2 : SymbolicObs := { initSym with player := some (5, 3), facing := Direction.left }
def s_L3 : SymbolicObs := { initSym with player := some (4, 3), facing := Direction.left }
def s_L4 : SymbolicObs := { initSym with player := some (3, 3), facing := Direction.left }
def s_L5 : SymbolicObs := { initSym with player := some (2, 3), facing := Direction.left }
def s_chest_adj : SymbolicObs := { initSym with player := some (1, 3), facing := Direction.left }

-- Phase 2: 开箱后
def s_postChest : SymbolicObs := { s_chest_adj with chests := [] }

def belief_after_open (b : BeliefState) : BeliefState :=
  { b with openedChests := CHEST_POS :: b.openedChests, hasKey := true, keys := b.keys + 1, step := b.step + 1 }

-- Phase 3: 从宝箱到出口
def s_R4 : SymbolicObs := { s_postChest with player := some (2, 3), facing := Direction.right }
def s_R5 : SymbolicObs := { s_postChest with player := some (3, 3), facing := Direction.right }
def s_U4 : SymbolicObs := { s_postChest with player := some (3, 2), facing := Direction.up }
def s_U5 : SymbolicObs := { s_postChest with player := some (3, 1), facing := Direction.up }
def s_U6 : SymbolicObs := { s_postChest with player := some (3, 0), facing := Direction.up }
def s_exit : SymbolicObs := { s_postChest with player := some (4, 0), facing := Direction.right }

/- ================================================================
   7. 阶段 1：从起点走到宝箱旁
   ================================================================ -/

theorem phase1_to_chest : Exec initSym initBelief
    [Action.right, Action.right, Action.right,
     Action.up, Action.up, Action.up,
     Action.left, Action.left, Action.left, Action.left, Action.left, Action.left]
    s_chest_adj { initBelief with step := 12 } := by
  -- define intermediate beliefs after each step
  let b0 := initBelief
  let b1 := { b0 with step := b0.step + 1 }
  let b2 := { b1 with step := b1.step + 1 }
  let b3 := { b2 with step := b2.step + 1 }
  let b4 := { b3 with step := b3.step + 1 }
  let b5 := { b4 with step := b4.step + 1 }
  let b6 := { b5 with step := b5.step + 1 }
  let b7 := { b6 with step := b6.step + 1 }
  let b8 := { b7 with step := b7.step + 1 }
  let b9 := { b8 with step := b8.step + 1 }
  let b10 := { b9 with step := b9.step + 1 }
  let b11 := { b10 with step := b10.step + 1 }
  let b12 := { b11 with step := b11.step + 1 }
  -- chain the steps with corresponding beliefs
  apply Exec.cons (step_right initSym b0 4 6 rfl rfl (by decide))
  apply Exec.cons (step_right s_R1 b1 5 6 rfl rfl (by decide))
  apply Exec.cons (step_right s_R2 b2 6 6 rfl rfl (by decide))
  apply Exec.cons (step_up s_R3 b3 7 6 rfl rfl (by decide))
  apply Exec.cons (step_up s_U1 b4 7 5 rfl rfl (by decide))
  apply Exec.cons (step_up s_U2 b5 7 4 rfl rfl (by decide))
  apply Exec.cons (step_left s_U3 b6 7 3 rfl rfl (by decide))
  apply Exec.cons (step_left s_L1 b7 6 3 rfl rfl (by decide))
  apply Exec.cons (step_left s_L2 b8 5 3 rfl rfl (by decide))
  apply Exec.cons (step_left s_L3 b9 4 3 rfl rfl (by decide))
  apply Exec.cons (step_left s_L4 b10 3 3 rfl rfl (by decide))
  apply Exec.cons (step_left s_L5 b11 2 3 rfl rfl (by decide))
  exact Exec.nil

/- ================================================================
   8. 阶段 2：打开宝箱获取钥匙
   ================================================================ -/

theorem phase2_open_chest (b : BeliefState) : Step s_chest_adj b Action.buttonA
    s_postChest (belief_after_open b) := by
  have hpos : s_chest_adj.player.isSome := by unfold s_chest_adj initSym; simp
  refine Step.openChest (c := CHEST_POS) hpos ?_ ?_
  · unfold s_chest_adj initSym; simp
  · unfold s_chest_adj initSym adjacent manhattan CHEST_POS; simp

/- ================================================================
   9. 阶段 3：从宝箱走到北侧出口
   ================================================================ -/

theorem phase3_to_exit (b : BeliefState) : Exec s_postChest b
    [Action.right, Action.right, Action.up, Action.up, Action.up, Action.right]
    s_exit { b with step := b.step + 6 } := by
  -- define intermediate beliefs
  let b0 := b
  let b1 := { b0 with step := b0.step + 1 }
  let b2 := { b1 with step := b1.step + 1 }
  let b3 := { b2 with step := b2.step + 1 }
  let b4 := { b3 with step := b3.step + 1 }
  let b5 := { b4 with step := b4.step + 1 }
  let b6 := { b5 with step := b5.step + 1 }
  apply Exec.cons
  · -- Step 1: right from (1,3) to (2,3)
    exact step_right s_postChest b0 1 3 (by unfold s_postChest s_chest_adj initSym; rfl) (by unfold s_postChest s_chest_adj initSym; simp) (by decide)
  · -- rest: [right, up, up, up, right]
    apply Exec.cons
    · exact step_right s_R4 b1 2 3 (by simp [s_R4, s_postChest, s_chest_adj, initSym]) (by simp [s_R4]) (by decide)
    · apply Exec.cons
      · exact step_up s_R5 b2 3 3 (by simp [s_R5, s_postChest, s_chest_adj, initSym]) (by simp [s_R5]) (by decide)
      · apply Exec.cons
        · exact step_up s_U4 b3 3 2 (by simp [s_U4, s_postChest, s_chest_adj, initSym]) (by simp [s_U4]) (by decide)
        · apply Exec.cons
          · exact step_up s_U5 b4 3 1 (by simp [s_U5, s_postChest, s_chest_adj, initSym]) (by simp [s_U5]) (by decide)
          · apply Exec.cons
            · exact step_right s_U6 b5 3 0 (by simp [s_U6, s_postChest, s_chest_adj, initSym]) (by simp [s_U6]) (by decide)
            · exact Exec.nil

/- ================================================================
   10. 主定理：Task 1 整体可达
   ================================================================

   注意：不需要单独的出门步骤。当玩家走到出口 tile (4,0) 时，
   任务目标 exitReached 已经达成（玩家在 EXIT_POSITIONS 中），
   无需再执行 Action.up 离开房间。
   ================================================================ -/

theorem task1_completable : TaskCompletable initSym initBelief task1Goal := by
  -- 规划 1：走到宝箱旁
  let plan1 : List Action :=
    [Action.right, Action.right, Action.right,
     Action.up, Action.up, Action.up,
     Action.left, Action.left, Action.left, Action.left, Action.left, Action.left]
  have h_phase1 : Exec initSym initBelief plan1 s_chest_adj { initBelief with step := 12 } := phase1_to_chest

  -- 规划 2：开箱（追加一个 buttonA）
  let plan2 : List Action := plan1 ++ [Action.buttonA]
  let b12 := { initBelief with step := 12 }
  have h_phase2 : Exec initSym initBelief plan2 s_postChest (belief_after_open b12) := by
    apply exec_append h_phase1
    apply Exec.cons (phase2_open_chest b12); exact Exec.nil

  -- 规划 3：走到出口（玩家到达 (4,0) 时已在 EXIT_POSITIONS 中）
  let plan3 : List Action :=
    [Action.right, Action.right, Action.up, Action.up, Action.up, Action.right]
  have h_all : Exec initSym initBelief (plan2 ++ plan3) s_exit ({ (belief_after_open b12) with step := (belief_after_open b12).step + 6 }) := by
    apply exec_append h_phase2 (phase3_to_exit (belief_after_open b12))

  -- 验证最终状态满足任务目标
  refine ⟨plan2 ++ plan3, s_exit, { (belief_after_open b12) with step := (belief_after_open b12).step + 6 }, h_all, ?_⟩
  unfold taskCompleted task1Goal
  simp [belief_after_open, s_exit, s_postChest, s_chest_adj, initSym, EXIT_POSITIONS]

end Task1
