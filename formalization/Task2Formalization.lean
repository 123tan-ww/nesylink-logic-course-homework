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
  simp
  simp[TRAP_POSITIONS] at ht
  simp[ROOM_H,ROOM_W]
  obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl:=ht
  all_goals (simp;simp[TRAP_POSITIONS])


/- ================================================================
   5. 三段式子目标组合可达性
   ================================================================ -/

def midSym1 : SymbolicObs :=
    {
      player    := some (2, 3)
      facing    := Direction.up
      monsters  := []
      chests    := [CHEST_POS]
      exits     := EXIT_POSITIONS
      traps     := TRAP_POSITIONS
      buttons   := []
      switches  := []
      grid      := buildTask2Grid
    }
def midBelief1 : BeliefState :=
    {
      hasKey      := false
      hasSword    := true
      keys        := 0
      gold        := 0
      openedChests  := []
      killedMonsters := [MONSTER_POS]
      pressedButtons := []
      step        := 7
    }

/-! 阶段 1：走向怪物并攻击 -/
theorem phase1_kill_monster :
    ∃ (plan : List Action),
      Exec initSym initBelief plan midSym1 midBelief1 := by
  -- 对应 Agent 的 killMonster 子目标
  let plan1 : List Action := [Action.left, Action.left, Action.left, Action.left, Action.left, Action.up, Action.buttonA]
  exists plan1
  -- h7：最后一步 buttonA 击杀怪物
  have h7 : Step
    { initSym with player := some (2, 3) , facing := Direction.up}
    { initBelief with step := 6 }
    Action.buttonA midSym1 midBelief1 := by
      have hpos: { initSym with player := some (2, 3) , facing := Direction.up}.player.isSome :=by simp
      have hmonster: (2,2) ∈ { initSym with player := some (2, 3) , facing := Direction.up}.monsters :=by simp;simp[initSym,MONSTER_POS]
      have hadjacent: adjacent ({ initSym with player := some (2, 3) , facing := Direction.up}.player.get hpos) (2,2) :=by simp[adjacent,manhattan]
      simp[midSym1,midBelief1]
      have hstep :=@Step.attackMonster ({ initSym with player := some (2, 3) , facing := Direction.up}) ({ initBelief with step := 6 }) (2,2) hpos hmonster hadjacent
      simp at hstep
      simp[initSym,initBelief] at hstep
      simp[initSym,initBelief]
      exact hstep
  have h_exec7 : Exec
    { initSym with player := some (2, 3) , facing := Direction.up}
     { initBelief with step := 6 }
    [Action.buttonA] midSym1 midBelief1 := by
    apply Exec.cons h7
    apply Exec.nil

  -- h6：Action.up 尝试向上，被阻挡 moveBlocked，坐标不变仅改朝向
  have h6 : Step
    { initSym with player := some (2, 3) ,facing := Direction.left}
     { initBelief with step := 5 }
    Action.up
    { initSym with player := some (2, 3) ,facing := Direction.up}
     { initBelief with step := 6 } := by
      have hpos: { initSym with player := some (2, 3) , facing := Direction.left}.player.isSome := by simp
      have hmove: isMoveAction Action.up :=by simp[isMoveAction]
      have hblocked: ¬ isSafeMove { initSym with player := some (2, 3) , facing := Direction.left}.grid (nextPosition ({ initSym with player := some (2, 3) , facing := Direction.left}.player.get hpos) Action.up) :=by
        simp[isSafeMove,inBounds,nextPosition,ROOM_H,ROOM_W,isBlocked,getTile,initSym,buildTask2Grid,TRAP_POSITIONS,MONSTER_POS,CHEST_POS,TILE_EMPTY,TILE_WALL,TILE_GAP,TILE_TRAP,TILE_MONSTER];
      have hstep:=@Step.moveBlocked { initSym with player := some (2, 3) ,facing := Direction.left} { initBelief with step := 5 } Action.up hpos hmove hblocked
      simp[initSym]
      simp[initSym] at hstep
      exact hstep
  have h_exec6 : Exec
    { initSym with player := some (2, 3) ,facing := Direction.left}
     { initBelief with step := 5 }
    [Action.up, Action.buttonA] midSym1 midBelief1 := by
    apply Exec.cons h6 h_exec7

  -- h5：第5次left (3,3) → (2,3) moveSafe
  have h5 : Step
    ({ initSym with player := some (3, 3), facing := Direction.left })
    { initBelief with step := 4 }
    Action.left
    ({ initSym with player := some (2, 3), facing := Direction.left })
    { initBelief with step := 5 } := by
      have hpos: ({ initSym with player := some (3, 3), facing := Direction.left }).player.isSome := by simp
      have hmove: isMoveAction Action.left := by simp [isMoveAction]
      have hsafe: isSafeMove ({ initSym with player := some (3, 3), facing := Direction.left }).grid
        (nextPosition (({ initSym with player := some (3, 3), facing := Direction.left }).player.get hpos) Action.left) := by
        simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, initSym, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP,TILE_CHEST,TILE_MONSTER]
      have hstep := @Step.moveSafe
        ({ initSym with player := some (3, 3), facing := Direction.left })
        { initBelief with step := 4 }
        Action.left hpos hmove hsafe
      simp [initSym, nextPosition] at hstep
      exact hstep
  have h_exec5 : Exec
    ({ initSym with player := some (3, 3), facing := Direction.left })
    { initBelief with step := 4 }
    [Action.left, Action.up, Action.buttonA] midSym1 midBelief1 := by
    apply Exec.cons h5 h_exec6

  -- h4：第4次left (4,3) → (3,3) moveSafe
  have h4 : Step
    ({ initSym with player := some (4, 3), facing := Direction.left })
    { initBelief with step := 3 }
    Action.left
    ({ initSym with player := some (3, 3), facing := Direction.left })
    { initBelief with step := 4 } := by
      have hpos: ({ initSym with player := some (4, 3), facing := Direction.left }).player.isSome := by simp
      have hmove: isMoveAction Action.left := by simp [isMoveAction]
      have hsafe: isSafeMove ({ initSym with player := some (4, 3), facing := Direction.left }).grid
        (nextPosition (({ initSym with player := some (4, 3), facing := Direction.left }).player.get hpos) Action.left) := by
        simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, initSym, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP,TILE_MONSTER,TILE_CHEST]
      have hstep := @Step.moveSafe
        ({ initSym with player := some (4, 3), facing := Direction.left })
        { initBelief with step := 3 }
        Action.left hpos hmove hsafe
      simp [initSym, nextPosition] at hstep
      exact hstep
  have h_exec4 : Exec
    ({ initSym with player := some (4, 3), facing := Direction.left })
    { initBelief with step := 3 }
    [Action.left, Action.left, Action.up, Action.buttonA] midSym1 midBelief1 := by
    apply Exec.cons h4 h_exec5

  -- h3：第3次left (5,3) → (4,3) moveSafe
  have h3 : Step
    ({ initSym with player := some (5, 3), facing := Direction.left })
    { initBelief with step := 2 }
    Action.left
    ({ initSym with player := some (4, 3), facing := Direction.left })
    { initBelief with step := 3 } := by
      have hpos: ({ initSym with player := some (5, 3), facing := Direction.left }).player.isSome := by simp
      have hmove: isMoveAction Action.left := by simp [isMoveAction]
      have hsafe: isSafeMove ({ initSym with player := some (5, 3), facing := Direction.left }).grid
        (nextPosition (({ initSym with player := some (5, 3), facing := Direction.left }).player.get hpos) Action.left) := by
        simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, initSym, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP,TILE_MONSTER,TILE_CHEST]
      have hstep := @Step.moveSafe
        ({ initSym with player := some (5, 3), facing := Direction.left })
        { initBelief with step := 2 }
        Action.left hpos hmove hsafe
      simp [initSym, nextPosition] at hstep
      exact hstep
  have h_exec3 : Exec
    ({ initSym with player := some (5, 3), facing := Direction.left })
    { initBelief with step := 2 }
    [Action.left, Action.left, Action.left, Action.up, Action.buttonA] midSym1 midBelief1 := by
    apply Exec.cons h3 h_exec4

  -- h2：第2次left (6,3) → (5,3) moveSafe
  have h2 : Step
    ({ initSym with player := some (6, 3), facing := Direction.left })
    { initBelief with step := 1 }
    Action.left
    ({ initSym with player := some (5, 3), facing := Direction.left })
    { initBelief with step := 2 } := by
      have hpos: ({ initSym with player := some (6, 3), facing := Direction.left }).player.isSome := by simp
      have hmove: isMoveAction Action.left := by simp [isMoveAction]
      have hsafe: isSafeMove ({ initSym with player := some (6, 3), facing := Direction.left }).grid
        (nextPosition (({ initSym with player := some (6, 3), facing := Direction.left }).player.get hpos) Action.left) := by
        simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, initSym, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP,TILE_MONSTER,TILE_CHEST]
      have hstep := @Step.moveSafe
        ({ initSym with player := some (6, 3), facing := Direction.left })
        { initBelief with step := 1 }
        Action.left hpos hmove hsafe
      simp [initSym, nextPosition] at hstep
      exact hstep
  have h_exec2 : Exec
    ({ initSym with player := some (6, 3), facing := Direction.left })
    { initBelief with step := 1 }
    [Action.left, Action.left, Action.left, Action.left, Action.up, Action.buttonA] midSym1 midBelief1 := by
    apply Exec.cons h2 h_exec3

  -- h1：第1次left (7,3) → (6,3) moveSafe
  have h1 : Step initSym initBelief Action.left
    ({ initSym with player := some (6, 3), facing := Direction.left })
    { initBelief with step := 1 } := by
      have hpos: initSym.player.isSome := by simp[initSym]
      have hmove: isMoveAction Action.left := by simp [isMoveAction]
      have hsafe: isSafeMove initSym.grid (nextPosition (initSym.player.get hpos) Action.left) := by
        simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, initSym, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP,TILE_CHEST,INIT_PLAYER,TILE_MONSTER,TILE_CHEST]
      have hstep := @Step.moveSafe initSym initBelief Action.left hpos hmove hsafe
      simp [initSym, nextPosition] at hstep
      exact hstep
  have h_exec1 : Exec initSym initBelief plan1 midSym1 midBelief1 := by
    apply Exec.cons h1 h_exec2
  exact h_exec1


def midSym2 : SymbolicObs :=
    {
      player    := some (2, 3)
      facing    := Direction.left
      monsters  := []
      chests    := []
      exits     := EXIT_POSITIONS
      traps     := TRAP_POSITIONS
      buttons   := []
      switches  := []
      grid      := buildTask2Grid
    }
def midBelief2 : BeliefState :=
    {
      hasKey      := true
      hasSword    := true
      keys        := 1
      gold        := 0
      openedChests  := [CHEST_POS]
      killedMonsters := [MONSTER_POS]
      pressedButtons := []
      step        := 9
    }

/-! 阶段 2：走向宝箱并开箱 -/
theorem phase2_open_chest :
    ∃ (plan : List Action),
      Exec midSym1 midBelief1 plan midSym2 midBelief2 := by
  -- 路径: left×2（走到宝箱相邻格）→ 按 A 开箱
  -- 对应 Agent 的 findChest 子目标
  -- 动作序列：左移（被阻挡，仅转朝向）→ 按键A开宝箱
  let plan2 : List Action := [Action.left, Action.buttonA]
  -- 第一步 left 后中间观测：坐标不变，朝向改为 left
  let midSym_mid : SymbolicObs :=
    { midSym1 with facing := Direction.left }
  let midBelief_mid : BeliefState :=
    { midBelief1 with step := midBelief1.step + 1 }
  -- 完整执行结束状态：宝箱移除、获得钥匙、记录已开宝箱
  exists plan2

  -- h2：第二步 buttonA 打开宝箱 openChest
  have h2 : Step midSym_mid midBelief_mid Action.buttonA midSym2 midBelief2 := by
    have hpos : midSym_mid.player.isSome := by simp [midSym_mid, midSym1]
    have hchest : CHEST_POS ∈ midSym_mid.chests := by simp [midSym_mid, midSym1]
    have hadjacent : adjacent (midSym_mid.player.get hpos) CHEST_POS := by
      simp [adjacent, manhattan, midSym_mid, CHEST_POS,midSym1]
    have hstep := @Step.openChest midSym_mid midBelief_mid CHEST_POS hpos hchest hadjacent
    simp [midSym2, midBelief2, CHEST_POS] at hstep ⊢
    exact hstep
  have exec_h2 : Exec midSym_mid midBelief_mid [Action.buttonA] midSym2 midBelief2 := by
    apply Exec.cons h2 Exec.nil

  -- h1：第一步 Action.left，目标宝箱格被阻挡，moveBlocked 仅改朝向
  have h1 : Step midSym1 midBelief1 Action.left midSym_mid midBelief_mid := by
    have hpos : midSym1.player.isSome := by simp [midSym1]
    have hmove : isMoveAction Action.left := by simp [isMoveAction]
    have hblocked : ¬ isSafeMove midSym1.grid (nextPosition (midSym1.player.get hpos) Action.left) := by
      simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile,midSym1,buildTask2Grid,TRAP_POSITIONS, TILE_MONSTER,TILE_WALL, TILE_GAP, TILE_TRAP, TILE_CHEST,MONSTER_POS,CHEST_POS]
    have hstep := @Step.moveBlocked midSym1 midBelief1 Action.left hpos hmove hblocked
    simp [midSym_mid, midBelief_mid, midSym1] at hstep ⊢
    exact hstep
  have exec_full : Exec midSym1 midBelief1 plan2 midSym2 midBelief2 := by
    apply Exec.cons h1 exec_h2
  exact Exec.cons h1 exec_h2



def finalSym : SymbolicObs :=
    {
      player    := some (0, 4)
      facing    := Direction.left
      monsters  := []
      chests    := []
      exits     := EXIT_POSITIONS
      traps     := TRAP_POSITIONS
      buttons   := []
      switches  := []
      grid      := buildTask2Grid
    }
def finalBelief : BeliefState :=
    {
      hasKey      := true
      hasSword    := true
      keys        := 1
      gold        := 0
      openedChests  := [CHEST_POS]
      killedMonsters := [MONSTER_POS]
      pressedButtons := []
      step        := 12
    }


/-! 阶段 3：走向出口 -/
theorem phase3_reach_exit :
    ∃ (plan : List Action),
      Exec midSym2 midBelief2 plan finalSym finalBelief := by
  -- 对应 Agent 的 goExit 子目标
  let plan3 : List Action := [Action.down, Action.left, Action.left]
  exists plan3

  -- 第三步：第二次left，移动到出口(0,4) moveExit
  let mid3_sym : SymbolicObs := { midSym2 with player := some (1,4), facing := Direction.left }
  let mid3_bel : BeliefState := { midBelief2 with step := 11 }
  have h_step3 : Step mid3_sym mid3_bel Action.left finalSym finalBelief := by
    have hpos : mid3_sym.player.isSome := by simp[mid3_sym]
    have hmove : isMoveAction Action.left := by simp[mid3_sym,isMoveAction]
    have hsafe : isSafeMove mid3_sym.grid (nextPosition (mid3_sym.player.get hpos) Action.left) := by
      simp [isSafeMove, nextPosition, EXIT_POSITIONS,mid3_sym,inBounds,ROOM_H,ROOM_W,isBlocked,getTile,buildTask2Grid,TRAP_POSITIONS,MONSTER_POS,CHEST_POS,TILE_EMPTY,TILE_WALL,TILE_GAP,TILE_TRAP,TILE_CHEST,TILE_MONSTER,midSym2]
    have hstep := @Step.moveSafe mid3_sym mid3_bel Action.left hpos hmove hsafe
    simp [finalSym, finalBelief, mid3_sym, mid3_bel] at hstep ⊢
    simp[midSym2,midBelief2] at hstep
    exact hstep
  have exec3 : Exec mid3_sym mid3_bel [Action.left] finalSym finalBelief := by
    apply Exec.cons h_step3 Exec.nil

  -- 第二步：第一次left，(2,4) → (1,4) moveSafe
  let mid2_sym : SymbolicObs := { midSym2 with player := some (2,4), facing := Direction.down }
  let mid2_bel : BeliefState := { midBelief2 with step := 10 }
  have h_step2 : Step mid2_sym mid2_bel Action.left mid3_sym mid3_bel := by
    have hpos : mid2_sym.player.isSome := by simp[mid2_sym]
    have hmove : isMoveAction Action.left := by simp[isMoveAction]
    have hsafe : isSafeMove mid2_sym.grid (nextPosition (mid2_sym.player.get hpos) Action.left) := by
      simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP, TILE_CHEST, TILE_MONSTER,mid2_sym,midSym2]
    have hstep := @Step.moveSafe mid2_sym mid2_bel Action.left hpos hmove hsafe
    simp [mid3_sym, mid3_bel, mid2_sym, mid2_bel, nextPosition] at hstep ⊢
    exact hstep
  have exec2 : Exec mid2_sym mid2_bel [Action.left, Action.left] finalSym finalBelief := by
    apply Exec.cons h_step2 exec3

  -- 第一步：down，(2,3) → (2,4) moveSafe
  have h_step1 : Step midSym2 midBelief2 Action.down mid2_sym mid2_bel := by
    have hpos : midSym2.player.isSome := by simp [midSym2]
    have hmove : isMoveAction Action.down := by simp[isMoveAction]
    have hsafe : isSafeMove midSym2.grid (nextPosition (midSym2.player.get hpos) Action.down) := by
      simp [isSafeMove, inBounds, nextPosition, ROOM_H, ROOM_W, isBlocked, getTile, buildTask2Grid, TRAP_POSITIONS, MONSTER_POS, CHEST_POS, TILE_EMPTY, TILE_WALL, TILE_GAP, TILE_TRAP, TILE_CHEST, TILE_MONSTER, midSym2]
    have hstep := @Step.moveSafe midSym2 midBelief2 Action.down hpos hmove hsafe
    simp [mid2_sym, mid2_bel, midSym2, nextPosition] at hstep ⊢
    exact hstep
  have exec_full : Exec midSym2 midBelief2 plan3 finalSym finalBelief := by
    apply Exec.cons h_step1 exec2
  exact exec_full

/-! 三阶段组合 → 任务整体可达 -/
theorem task2_completable :
    TaskCompletable initSym initBelief task2Goal := by
  -- 用 Exec 的组合性拼接三段计划
  -- plan = plan1 ++ plan2 ++ plan3
  simp[TaskCompletable,task2Goal,taskCompleted]
  rcases phase1_kill_monster with ⟨plan1, h_exec1⟩
  rcases phase2_open_chest with ⟨plan2, h_exec2⟩
  rcases phase3_reach_exit with ⟨plan3, h_exec3⟩
  exists (plan1 ++ plan2 ++ plan3),finalSym,finalBelief
  constructor
  · have h12 := exec_append h_exec1 h_exec2
    have h123 := exec_append h12 h_exec3
    exact h123
  · simp[finalSym,finalBelief,EXIT_POSITIONS]
end Task2
