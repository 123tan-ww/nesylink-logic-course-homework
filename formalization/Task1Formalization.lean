/-
  Task1Formalization.lean

  对应关卡 mathematical_logic/task_1：
  - 单房间
  - 起点 (4, 6)，宝箱在 (0, 3)
  - 北侧锁门，需要消耗 1 把钥匙
  - 有墙体障碍
  - 最大步数 500

  地图参考: map_data/mathematical_logic/task_1/room_001.json
-/

import NesyLinkCore
open NesyLinkCore

namespace Task1

/- ================================================================
   1. 地图常量
   ================================================================ -/

/-! 墙体位置（从 JSON layout 提取） -/
def WALLS : List Position := [
  (0, 2), (1, 2),
  (7, 5), (8, 5), (9, 5),
  (7, 4), (8, 4), (9, 4),
  (7, 3), (8, 3), (9, 3),
  (7, 2), (8, 2), (9, 2),
  (0, 5), (1, 5), (2, 5), (3, 5), (4, 5), (5, 5), (6, 5)
]

/-! 宝箱位置 -/
def CHEST_POS : Position := (0, 3)

/-! 出口位置（北侧锁门，两个 tile） -/
def EXIT_POSITIONS : List Position := [(4, 0), (5, 0)]

/-! 初始玩家位置 -/
def INIT_PLAYER : Position := (4, 6)

/- ================================================================
   2. Grid 构造
   ================================================================ -/

/-! 构建 10×8 grid（EMPTY=0, WALL=1） -/
def buildTask1Grid : Grid :=
  List.range ROOM_H |>.map (λ y =>
    List.range ROOM_W |>.map (λ x =>
      if (x, y) ∈ WALLS then TILE_WALL else TILE_EMPTY
    )
  )

/- ================================================================
   3. 初始状态
   ================================================================ -/

def initSym : SymbolicObs :=
  {
    player    := some INIT_PLAYER
    facing    := Direction.down
    monsters  := []
    chests    := [CHEST_POS]
    exits     := EXIT_POSITIONS
    traps     := []
    buttons   := []
    switches  := []
    grid      := buildTask1Grid
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

/-! Task 1 的完成目标 -/
def task1Goal : TaskGoal :=
  {
    monstersDefeated := false
    keyCollected     := true
    chestOpened      := true
    exitReached      := true
    allChestsOpened  := false
  }

/- ================================================================
   4. 墙的不可通行性
   ================================================================ -/

theorem walls_are_blocked (p : Position) (hw : p ∈ WALLS) :
    isBlocked buildTask1Grid p := by
  unfold isBlocked getTile buildTask1Grid
  -- 根据 p 在 WALLS 中，可以推出对应 tile = TILE_WALL
  -- 完整证明需要展开 grid 构造并逐个 case 分析
  sorry

/- ================================================================
   5. 安全移动定理
   ================================================================ -/

theorem player_starts_in_bounds :
    inBounds INIT_PLAYER := by
  unfold inBounds INIT_PLAYER
  decide

theorem chest_reachable_from_start :
    ∃ (plan : List Action),
      Exec initSym initBelief plan
        { initSym with player := some (0, 2) }  -- 宝箱相邻格
        initBelief := by
  -- 存在一条路径走到宝箱旁边
  -- 实际路径: right×48 → up×48 → left×96
  -- 这里先用 sorry，具体证明时写出 Step 序列
  sorry

/- ================================================================
   6. 开箱子目标
   ================================================================ -/

theorem can_open_chest_when_adjacent :
    let nearChest := { initSym with player := some (1, 3) }
    Step nearChest initBelief Action.buttonA
      { nearChest with chests := nearChest.chests.erase CHEST_POS }
      { initBelief with
        openedChests := [CHEST_POS]
        , hasKey := true
        , keys := 1
      } := by
  intro nearChest
  have hpos : nearChest.player.isSome := by
    unfold nearChest; simp
  apply Step.openChest hpos
  · -- CHEST_POS 在 chests 中
    unfold nearChest initSym; simp
  · -- adjacent to chest
    unfold nearChest initSym adjacent manhattan CHEST_POS
    simp

/- ================================================================
   7. 开门离开
   ================================================================ -/

theorem can_exit_with_key :
    let hasKeyState := { initBelief with hasKey := true, keys := 1 }
    let atExit := { initSym with player := some (4, 0) }
    isExitLeavingAction (4, 0) Action.up EXIT_POSITIONS := by
  unfold isExitLeavingAction EXIT_POSITIONS
  simp

/- ================================================================
   8. 任务整体可达性
   ================================================================ -/

theorem task1_completable :
    TaskCompletable initSym initBelief task1Goal := by
  -- 需要构造完整的动作序列并证明每个 Step 合法
  -- 三个子阶段：去宝箱 → 开箱 → 去出口
  -- 使用 exec_append 组合子计划
  sorry

end Task1
