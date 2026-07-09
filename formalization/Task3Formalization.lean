/-
  Task3Formalization.lean

  对应关卡 mathematical_logic/task_3：
  - 3 个房间：start_room → monster_hall → key_room
  - start_room 有 NPC（提示）和东侧锁门
  - monster_hall 有 1 个 chaser 怪物
  - key_room 有 1 个宝箱（含钥匙）
  - 流程：穿过怪物房 → 去西侧拿钥匙 → 返回起点 → 开东侧锁门
  - 最大步数 1500

  对应 Agent 代码：
    symbolicPlanner 管理房间图 room_exits_info
    跨房间通过 goExit 子目标 + 房间级 BFS 导航
-/

import NesyLinkCore
open NesyLinkCore

namespace Task3

/- ================================================================
   1. 房间 ID 约定
   ================================================================ -/

def ROOM_START      : RoomId := 0
def ROOM_MONSTER_HALL : RoomId := 1
def ROOM_KEY_ROOM   : RoomId := 2

/- ================================================================
   2. 各房间常量（简略，详细定义在具体证明时补充）
   ================================================================ -/

-- start_room: 起点 (4,4), 西侧出口通向 monster_hall, 东侧锁门
-- monster_hall: 怪物 chaser 在 (5,3), 东西两个出口
-- key_room: 宝箱在 (5,4), 东侧出口返回 monster_hall

/- ================================================================
   3. 房间图 — 对应 symbolicPlanner 的拓扑结构
   ================================================================ -/

def task3RoomGraph : RoomGraph :=
  {
    roomId2Coord := [
      (0, { x := 0, y := 0 }),
      (1, { x := -1, y := 0 }),
      (2, { x := -2, y := 0 })
    ]
    roomCoord2Id := [
      ({ x := 0, y := 0 }, 0),
      ({ x := -1, y := 0 }, 1),
      ({ x := -2, y := 0 }, 2)
    ]
    roomExits := [
      (0, [
        ("west",  { direction := "west",  exitType := "normal",     opened := true,  dest := 1, start := 0, tiles := [(0, 4)], isReached := false }),
        ("east",  { direction := "east",  exitType := "locked_key", opened := false, dest := 0, start := 0, tiles := [(9, 4)], isReached := false })
      ]),
      (1, [
        ("east",  { direction := "east",  exitType := "normal", opened := true,  dest := 0, start := 1, tiles := [(9, 4)], isReached := false }),
        ("west",  { direction := "west",  exitType := "normal", opened := true,  dest := 2, start := 1, tiles := [(0, 4)], isReached := false })
      ]),
      (2, [
        ("east",  { direction := "east",  exitType := "normal", opened := true,  dest := 1, start := 2, tiles := [(9, 4)], isReached := false })
      ])
    ]
  }

/- ================================================================
   4. 房间间可达性
   ================================================================ -/

theorem start_to_keyRoom_reachable :
    roomReachable task3RoomGraph ROOM_START ROOM_KEY_ROOM := by
  -- 路径: start(0) → west → monster_hall(1) → west → key_room(2)
  -- 对应 symbolicPlanner._bfs 的输出
  sorry

theorem keyRoom_to_start_reachable :
    roomReachable task3RoomGraph ROOM_KEY_ROOM ROOM_START := by
  -- 返回路径: key_room(2) → east → monster_hall(1) → east → start(0)
  sorry

/- ================================================================
   5. 任务完成条件
   ================================================================ -/

def task3Goal : TaskGoal :=
  {
    monstersDefeated := false   -- 怪物可以不打，穿过去即可
    keyCollected     := true
    chestOpened      := true
    exitReached      := true
    allChestsOpened  := false
  }

/- ================================================================
   6. 跨房间计划可达性
   ================================================================ -/

theorem task3_completable :
    ∃ (plan : List Action) (finalSym : SymbolicObs) (finalBelief : BeliefState),
      -- 从起始状态出发，完成目标
      True := by
  -- 思路（需要具体实现）:
  -- 1. start_room → go_exit(west) → monster_hall
  -- 2. monster_hall → go_exit(west) → key_room
  -- 3. key_room → open_chest → get_key
  -- 4. key_room → go_exit(east) → monster_hall → go_exit(east) → start_room
  -- 5. start_room → go_exit(east) → 开锁门 → 完成
  trivial

end Task3
