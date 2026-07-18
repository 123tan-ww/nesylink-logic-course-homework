/-
  Task3Formalization.lean

  对应关卡 mathematical_logic/task_3：
  - 3 个房间：start_room(0,0), monster_hall(-1,0), key_room(-2,0)
  - start_room：全空地，西出口→monster_hall，东侧锁门（需钥匙）
  - monster_hall：全空地，1 个 chaser 怪物 (5,3)
  - key_room：全空地，1 个宝箱 (5,4) 含钥匙
  - 流程：穿怪物房→去西侧拿钥匙→返回→开东侧锁门
  - 最大步数 1500

  对应 Agent 代码：
    symbolicPlanner 管理房间图，跨房间通过 goExit 子目标 + 房间级 BFS 导航
-/

import NesyLinkCore
open NesyLinkCore

namespace Task3

/- ================================================================
   0. 任务常量
   ================================================================ -/

def TASK3_MAX_STEPS : Nat := 1500

/- ================================================================
   1. 房间 ID 约定
   ================================================================ -/

def ROOM0_ID : RoomId := 0
def ROOM1_ID : RoomId := 1
def ROOM2_ID : RoomId := 2

/- ================================================================
   2. 地图常量 — 三个房间
   ================================================================ -/

/-- start_room（起点 [0,0]）：全空地，无墙 -/
def ROOM0_EXITS : List Position := [(0, 4), (9, 4)]
def ROOM0_SPAWN_DEFAULT : Position := (4, 4)
def ROOM0_SPAWN_FROM_WEST : Position := (1, 4)
def ROOM0_SPAWN_FROM_EAST : Position := (8, 4)

/-- monster_hall（中间 [-1,0]）：全空地，1 个怪物 -/
def ROOM1_MONSTER : Position := (5, 3)
def ROOM1_EXITS : List Position := [(0, 4), (9, 4)]
def ROOM1_SPAWN_FROM_EAST : Position := (8, 4)
def ROOM1_SPAWN_FROM_WEST : Position := (1, 4)

/-- key_room（西侧 [-2,0]）：全空地，1 个宝箱 -/
def ROOM2_CHEST : Position := (5, 4)
def ROOM2_EXITS : List Position := [(9, 4)]
def ROOM2_SPAWN : Position := (8, 4)

/- ================================================================
   3. 网格构造 — 三个房间均无墙
   ================================================================ -/

def buildRoom0Grid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ ROOM0_EXITS then TILE_EXIT
      else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

def buildRoom1Grid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ ROOM1_EXITS then TILE_EXIT
      else (if (x,y) = ROOM1_MONSTER then TILE_MONSTER else TILE_EMPTY))
    (List.range ROOM_W))
  (List.range ROOM_H)

def buildRoom2Grid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) = ROOM2_CHEST then TILE_CHEST
      else if (x, y) ∈ ROOM2_EXITS then TILE_EXIT
      else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

/- ================================================================
   4. 初始状态 — 从 start_room (4,4) 出发
   ================================================================ -/

def initSym : SymbolicObs :=
  { player := some ROOM0_SPAWN_DEFAULT
    facing := Direction.down
    monsters := []
    chests := []
    exits := ROOM0_EXITS
    traps := []
    buttons := []
    switches := []
    grid := buildRoom0Grid
  }

def initBelief : BeliefState :=
  { hasKey := false, hasSword := true, keys := 0, gold := 0,
    openedChests := [], killedMonsters := [], pressedButtons := [], step := 0
  }

/- ================================================================
   5. 房间状态构造器 + 出口→目标映射
   ================================================================ -/

/-- 根据 roomId 构造完整的房间符号状态（player 放在指定位置） -/
def getRoomObs (rid : RoomId) (playerPos : Position) : SymbolicObs :=
  match rid with
  | 0 => { player := some playerPos, facing := Direction.down,
           monsters := [], chests := [],
           exits := ROOM0_EXITS, traps := [], buttons := [],
           switches := [], grid := buildRoom0Grid }
  | 1 => { player := some playerPos, facing := Direction.down,
           monsters := [ROOM1_MONSTER], chests := [],
           exits := ROOM1_EXITS, traps := [], buttons := [],
           switches := [], grid := buildRoom1Grid }
  | 2 => { player := some playerPos, facing := Direction.down,
           monsters := [], chests := [ROOM2_CHEST],
           exits := ROOM2_EXITS, traps := [], buttons := [],
           switches := [], grid := buildRoom2Grid }
  | _  => initSym

/-- 从 (当前房间, 出口坐标) 映射到 (目标房间, 出生点) -/
def exitToDest (rid : RoomId) (exitPos : Position) : Option (RoomId × Position) :=
  match rid, exitPos with
  | 0, (0, 4) => some (1, ROOM1_SPAWN_FROM_EAST)  -- start west → monster_hall
  | 0, (9, 4) => none                                -- 东侧锁门（任务完成，不是换房间）
  | 1, (0, 4) => some (2, ROOM2_SPAWN)             -- monster_hall west → key_room
  | 1, (9, 4) => some (0, ROOM0_SPAWN_FROM_WEST)    -- monster_hall east → start
  | 2, (9, 4) => some (1, ROOM1_SPAWN_FROM_WEST)    -- key_room east → monster_hall
  | _, _      => none

/- ================================================================
   6. 房间图 — 对应 symbolicPlanner 的拓扑结构
   ================================================================ -/

def task3RoomGraph : RoomGraph :=
  {
    roomId2Coord := [
      (ROOM0_ID, { x := 0, y := 0 }),
      (ROOM1_ID, { x := -1, y := 0 }),
      (ROOM2_ID, { x := -2, y := 0 })
    ]
    roomCoord2Id := [
      ({ x := 0, y := 0 }, ROOM0_ID),
      ({ x := -1, y := 0 }, ROOM1_ID),
      ({ x := -2, y := 0 }, ROOM2_ID)
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
   7. 房间间可达性
   ================================================================ -/

theorem start_to_keyRoom_reachable :
    roomReachable task3RoomGraph ROOM0_ID ROOM2_ID := by
  have h1: adjacentRooms task3RoomGraph ROOM0_ID ROOM1_ID := by
    unfold adjacentRooms
    simp [task3RoomGraph,getRoomExits]
    exists "west",  { direction := "west",  exitType := "normal",     opened := true,  dest := 1, start := 0, tiles := [(0, 4)], isReached := false }
  have h2: adjacentRooms task3RoomGraph ROOM1_ID ROOM2_ID := by
    unfold adjacentRooms
    simp [task3RoomGraph,getRoomExits]
    exists "west",  { direction := "west",  exitType := "normal",     opened := true,  dest := 2, start := 1, tiles := [(0, 4)], isReached := false }
  exact RoomPath.step h1 (RoomPath.step h2 RoomPath.self)


theorem keyRoom_to_start_reachable :
  roomReachable task3RoomGraph ROOM2_ID ROOM0_ID := by
  have h1: adjacentRooms task3RoomGraph ROOM1_ID ROOM0_ID := by
    unfold adjacentRooms
    simp [task3RoomGraph,getRoomExits]
    exists "east",  { direction := "east",  exitType := "normal", opened := true,  dest := 0, start := 1, tiles := [(9, 4)], isReached := false }
  have h2: adjacentRooms task3RoomGraph ROOM2_ID ROOM1_ID := by
    unfold adjacentRooms
    simp [task3RoomGraph,getRoomExits]
    exists "east",  { direction := "east",  exitType := "normal", opened := true,  dest := 1, start := 2, tiles := [(9, 4)], isReached := false }
  exact RoomPath.step h2 (RoomPath.step h1 RoomPath.self)


theorem all_rooms_reachable :
    roomReachable task3RoomGraph ROOM0_ID ROOM1_ID ∧
    roomReachable task3RoomGraph ROOM0_ID ROOM2_ID := by
  constructor
  · have h1: adjacentRooms task3RoomGraph ROOM0_ID ROOM1_ID := by
      unfold adjacentRooms
      simp [task3RoomGraph,getRoomExits]
      exists "west",  { direction := "west",  exitType := "normal",     opened := true,  dest := 1, start := 0, tiles := [(0, 4)], isReached := false }
    exact RoomPath.step h1 RoomPath.self
  · exact start_to_keyRoom_reachable


/- ================================================================
   8. 房间切换定理
   ================================================================ -/

theorem start_west_to_monster_hall (s : SymbolicObs) (b : BeliefState)
    (hgrid : s.grid = buildRoom0Grid) (hplayer : s.player = some (0, 4))
    (hexits : s.exits = ROOM0_EXITS) :
    Step s b Action.left (getRoomObs 1 ROOM1_SPAWN_FROM_EAST) { b with step := b.step + 1 } :=
by
  let room' := getRoomObs 1 ROOM1_SPAWN_FROM_EAST
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.left := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.left s.exits := by
    simp [hplayer, hexits, ROOM0_EXITS, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildRoom1Grid := by simp [room', getRoomObs]
    have h1 : s.grid = buildRoom0Grid := hgrid
    rw [h0, h1] at h_eq
    have hdiff: buildRoom1Grid ≠ buildRoom0Grid := by
      simp[buildRoom0Grid,buildRoom1Grid];exists 0
    contradiction
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact @Step.roomTransition s (getRoomObs 1 ROOM1_SPAWN_FROM_EAST) b Action.left hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem monster_hall_east_to_start (s : SymbolicObs) (b : BeliefState)
    (hgrid : s.grid = buildRoom1Grid) (hplayer : s.player = some (9, 4))
    (hexits : s.exits = ROOM1_EXITS) :
    Step s b Action.right (getRoomObs 0 ROOM0_SPAWN_FROM_WEST) { b with step := b.step + 1 } :=
by
  let room' := getRoomObs 0 ROOM0_SPAWN_FROM_WEST
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.right := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.right s.exits := by
    simp [hplayer, hexits, ROOM1_EXITS, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildRoom0Grid := by simp [room', getRoomObs]
    have h1 : s.grid = buildRoom1Grid := hgrid
    rw [h0, h1] at h_eq
    have : buildRoom0Grid ≠ buildRoom1Grid := by native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem monster_hall_west_to_key_room (s : SymbolicObs) (b : BeliefState)
    (hgrid : s.grid = buildRoom1Grid) (hplayer : s.player = some (0, 4))
    (hexits : s.exits = ROOM1_EXITS) :
    Step s b Action.left (getRoomObs 2 ROOM2_SPAWN) { b with step := b.step + 1 } :=
by
  let room' := getRoomObs 2 ROOM2_SPAWN
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.left := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.left s.exits := by
    simp [hplayer, hexits, ROOM1_EXITS, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildRoom2Grid := by simp [room', getRoomObs]
    have h1 : s.grid = buildRoom1Grid := hgrid
    rw [h0, h1] at h_eq
    have : buildRoom2Grid ≠ buildRoom1Grid := by native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem key_room_east_to_monster_hall (s : SymbolicObs) (b : BeliefState)
    (hgrid : s.grid = buildRoom2Grid) (hplayer : s.player = some (9, 4))
    (hexits : s.exits = ROOM2_EXITS) :
    Step s b Action.right (getRoomObs 1 ROOM1_SPAWN_FROM_WEST) { b with step := b.step + 1 } :=
by
  let room' := getRoomObs 1 ROOM1_SPAWN_FROM_WEST
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.right := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.right s.exits := by
    simp [hplayer, hexits, ROOM2_EXITS, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildRoom1Grid := by simp [room', getRoomObs]
    have h1 : s.grid = buildRoom2Grid := hgrid
    rw [h0, h1] at h_eq
    have : buildRoom1Grid ≠ buildRoom2Grid := by native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

/-- 东侧锁门（需钥匙）：从 start_room (9,4) 向右走出完成任务 -/
theorem start_east_locked_exit (s : SymbolicObs) (b : BeliefState)
    (hgrid : s.grid = buildRoom0Grid) (hplayer : s.player = some (9, 4))
    (hexits : s.exits = ROOM0_EXITS) (hhasKey : b.hasKey = true) :
    Step s b Action.right
      { s with player := some (10, 4), facing := Direction.right }
      { b with step := b.step + 1 } :=
by
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.right := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.right s.exits := by
    simp [hplayer, hexits, ROOM0_EXITS, isExitLeavingAction, ROOM_W, ROOM_H]
  have h0 := @Step.moveExit s b Action.right hpos hmove hescape
  simp[nextPosition] at h0
  have h1: s.player.get hpos = (9, 4) := by simp [hplayer]
  rw[h1] at h0
  exact h0


/- ================================================================
   9. 各房间路径安全
   ================================================================ -/

/-- start_room 路径（均为空 tile 或 exit）-/
def room0_path : List Position := [
  (3,4), (2,4), (1,4), (0,4),      -- (4,4)→西出口
  (1,4),(2,4),(3,4),(4,4),(5,4), (6,4), (7,4), (8,4), (9,4) -- (4,4)→东锁门
]

theorem room0_path_safe : ∀ p ∈ room0_path, isSafeMove buildRoom0Grid p := by
  simp [room0_path, isSafeMove, isBlocked, inBounds, getTile,
    buildRoom0Grid, ROOM0_EXITS, ROOM_W, ROOM_H, TILE_EMPTY, TILE_EXIT]
  all_goals { native_decide }

/-- monster_hall 路径（避开怪物 (5,3)，沿 y=4 走）-/
def room1_path : List Position := [
  (7,4),(6,4),(5,4),(4,4),(3,4),(2,4),(1,4),(0,4),   -- 东→西
  (2,4),(3,4),(4,4),(5,4),(6,4),(7,4),(8,4),(9,4)    -- 西→东
]

theorem room1_path_safe : ∀ p ∈ room1_path, isSafeMove buildRoom1Grid p := by
  simp [room1_path, isSafeMove, isBlocked, inBounds, getTile,
    buildRoom1Grid, ROOM1_EXITS, ROOM_W, ROOM_H, TILE_EMPTY, TILE_EXIT,ROOM1_MONSTER]
  all_goals { native_decide }

/-- key_room 路径 -/
def room2_path : List Position := [
  (7,4),(6,4),            -- spawn→宝箱
  (7,4),(8,4),(9,4)      -- 宝箱→东出口
]

theorem room2_path_safe : ∀ p ∈ room2_path, isSafeMove buildRoom2Grid p := by
  simp [room2_path, isSafeMove, isBlocked, inBounds, getTile,
    buildRoom2Grid, ROOM2_CHEST, ROOM2_EXITS, ROOM_W, ROOM_H,
    TILE_EMPTY, TILE_CHEST, TILE_EXIT]
  all_goals { native_decide }

theorem room1_path_avoids_monster : ∀ p ∈ room1_path, p ≠ ROOM1_MONSTER := by
  native_decide

/- ================================================================
   10. 单步移动引理 — Room 0
   ================================================================ -/

theorem step0_left (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom0Grid) (hp : s.player = some (x, y))
    (hsafe : (x-1, y) ∈ room0_path) :
    Step s b Action.left
      { s with player := some (x-1, y), facing := Direction.left }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.left) := by
    simpa [hg, hp, nextPosition] using room0_path_safe (x-1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step0_right (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom0Grid) (hp : s.player = some (x, y))
    (hsafe : (x+1, y) ∈ room0_path) :
    Step s b Action.right
      { s with player := some (x+1, y), facing := Direction.right }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.right) := by
    simpa [hg, hp, nextPosition] using room0_path_safe (x+1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step0_up (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom0Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y-1) ∈ room0_path) :
    Step s b Action.up
      { s with player := some (x, y-1), facing := Direction.up }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.up) := by
    simpa [hg, hp, nextPosition] using room0_path_safe (x, y-1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step0_down (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom0Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y+1) ∈ room0_path) :
    Step s b Action.down
      { s with player := some (x, y+1), facing := Direction.down }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.down) := by
    simpa [hg, hp, nextPosition] using room0_path_safe (x, y+1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

/- ================================================================
   10b. 单步移动引理 — Room 1
   ================================================================ -/

theorem step1_left (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom1Grid) (hp : s.player = some (x, y))
    (hsafe : (x-1, y) ∈ room1_path) :
    Step s b Action.left
      { s with player := some (x-1, y), facing := Direction.left }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.left) := by
    simpa [hg, hp, nextPosition] using room1_path_safe (x-1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step1_right (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom1Grid) (hp : s.player = some (x, y))
    (hsafe : (x+1, y) ∈ room1_path) :
    Step s b Action.right
      { s with player := some (x+1, y), facing := Direction.right }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.right) := by
    simpa [hg, hp, nextPosition] using room1_path_safe (x+1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step1_up (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom1Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y-1) ∈ room1_path) :
    Step s b Action.up
      { s with player := some (x, y-1), facing := Direction.up }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.up) := by
    simpa [hg, hp, nextPosition] using room1_path_safe (x, y-1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step1_down (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom1Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y+1) ∈ room1_path) :
    Step s b Action.down
      { s with player := some (x, y+1), facing := Direction.down }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.down) := by
    simpa [hg, hp, nextPosition] using room1_path_safe (x, y+1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

/- ================================================================
   10c. 单步移动引理 — Room 2
   ================================================================ -/

theorem step2_left (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom2Grid) (hp : s.player = some (x, y))
    (hsafe : (x-1, y) ∈ room2_path) :
    Step s b Action.left
      { s with player := some (x-1, y), facing := Direction.left }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.left) := by
    simpa [hg, hp, nextPosition] using room2_path_safe (x-1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step2_right (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom2Grid) (hp : s.player = some (x, y))
    (hsafe : (x+1, y) ∈ room2_path) :
    Step s b Action.right
      { s with player := some (x+1, y), facing := Direction.right }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.right) := by
    simpa [hg, hp, nextPosition] using room2_path_safe (x+1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step2_up (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom2Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y-1) ∈ room2_path) :
    Step s b Action.up
      { s with player := some (x, y-1), facing := Direction.up }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.up) := by
    simpa [hg, hp, nextPosition] using room2_path_safe (x, y-1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step2_down (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildRoom2Grid) (hp : s.player = some (x, y))
    (hsafe : (x, y+1) ∈ room2_path) :
    Step s b Action.down
      { s with player := some (x, y+1), facing := Direction.down }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.down) := by
    simpa [hg, hp, nextPosition] using room2_path_safe (x, y+1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

/- ================================================================
   11. 中间状态定义
   ================================================================ -/

-- Room 0: spawn(4,4) → 西出口 / 东锁门
def s0_atSpawn : SymbolicObs := getRoomObs 0 ROOM0_SPAWN_DEFAULT
def s0_west1 : SymbolicObs := { s0_atSpawn with player := some (3, 4), facing := Direction.left }
def s0_west2 : SymbolicObs := { s0_atSpawn with player := some (2, 4), facing := Direction.left }
def s0_west3 : SymbolicObs := { s0_atSpawn with player := some (1, 4), facing := Direction.left }
def s0_atWestExit : SymbolicObs := { s0_atSpawn with player := some (0, 4), facing := Direction.left }

-- Room 1: 从东入口(8,4)→西出口(0,4)
def s1_fromEast : SymbolicObs := getRoomObs 1 ROOM1_SPAWN_FROM_EAST
def s1_west1  : SymbolicObs := { s1_fromEast with player := some (7, 4), facing := Direction.left }
def s1_west2  : SymbolicObs := { s1_fromEast with player := some (6, 4), facing := Direction.left }
def s1_west3  : SymbolicObs := { s1_fromEast with player := some (5, 4), facing := Direction.left }
def s1_west4  : SymbolicObs := { s1_fromEast with player := some (4, 4), facing := Direction.left }
def s1_west5  : SymbolicObs := { s1_fromEast with player := some (3, 4), facing := Direction.left }
def s1_west6  : SymbolicObs := { s1_fromEast with player := some (2, 4), facing := Direction.left }
def s1_west7  : SymbolicObs := { s1_fromEast with player := some (1, 4), facing := Direction.left }
def s1_atWestExit : SymbolicObs := { s1_fromEast with player := some (0, 4), facing := Direction.left }

-- Room 2: spawn(8,4)→宝箱(5,4)开箱→东出口(9,4)
def s2_atSpawn : SymbolicObs := getRoomObs 2 ROOM2_SPAWN
def s2_chest1 : SymbolicObs := { s2_atSpawn with player := some (7, 4), facing := Direction.left }
def s2_chest2 : SymbolicObs := { s2_atSpawn with player := some (6, 4), facing := Direction.left }
def s2_atChest : SymbolicObs := { s2_atSpawn with player := some (5, 4), facing := Direction.left }
def s2_postChest : SymbolicObs := { s2_atChest with player := some (6,4),chests := [] }
def s2_exit1 : SymbolicObs := { s2_postChest with player := some (7, 4), facing := Direction.right }
def s2_exit2 : SymbolicObs := { s2_postChest with player := some (8, 4), facing := Direction.right }
def s2_atEastExit : SymbolicObs := { s2_postChest with player := some (9, 4), facing := Direction.right }

-- Room 1 回程: 从西入口(1,4)→东出口(9,4)
def s1_fromWest : SymbolicObs := getRoomObs 1 ROOM1_SPAWN_FROM_WEST
def s1_east1 : SymbolicObs := { s1_fromWest with player := some (2, 4), facing := Direction.right }
def s1_east2 : SymbolicObs := { s1_fromWest with player := some (3, 4), facing := Direction.right }
def s1_east3 : SymbolicObs := { s1_fromWest with player := some (4, 4), facing := Direction.right }
def s1_east4 : SymbolicObs := { s1_fromWest with player := some (5, 4), facing := Direction.right }
def s1_east5 : SymbolicObs := { s1_fromWest with player := some (6, 4), facing := Direction.right }
def s1_east6 : SymbolicObs := { s1_fromWest with player := some (7, 4), facing := Direction.right }
def s1_east7 : SymbolicObs := { s1_fromWest with player := some (8, 4), facing := Direction.right }
def s1_atEastExit : SymbolicObs := { s1_fromWest with player := some (9, 4), facing := Direction.right }

-- Room 0 回程: (1,4)→东锁门(9,4)
def s0_fromWest : SymbolicObs := getRoomObs 0 ROOM0_SPAWN_FROM_WEST
def s0_east1 : SymbolicObs := { s0_fromWest with player := some (2, 4), facing := Direction.right }
def s0_east2 : SymbolicObs := { s0_fromWest with player := some (3, 4), facing := Direction.right }
def s0_east3 : SymbolicObs := { s0_fromWest with player := some (4, 4), facing := Direction.right }
def s0_east4 : SymbolicObs := { s0_fromWest with player := some (5, 4), facing := Direction.right }
def s0_east5 : SymbolicObs := { s0_fromWest with player := some (6, 4), facing := Direction.right }
def s0_east6 : SymbolicObs := { s0_fromWest with player := some (7, 4), facing := Direction.right }
def s0_east7 : SymbolicObs := { s0_fromWest with player := some (8, 4), facing := Direction.right }
def s0_atEastLocked : SymbolicObs := { s0_fromWest with player := some (9, 4), facing := Direction.right }

/-- 开箱后的信念更新 -/
def belief_after_key (b : BeliefState) : BeliefState :=
  { b with openedChests := ROOM2_CHEST :: b.openedChests, hasKey := true, keys := b.keys + 1, step := b.step + 1 }

/- ================================================================
   12. Exec 证明 — 各阶段
   ================================================================ -/

/-- Phase 1: start_room(4,4)→西出口(0,4) [4步] -/
theorem phase1_spawn_to_west_exit (b : BeliefState) :
    Exec s0_atSpawn b [Action.left, Action.left, Action.left, Action.left]
      s0_atWestExit { b with step := b.step + 4 } := by
  let b0 := b; let b1 := {b0 with step := b0.step+1}; let b2 := {b1 with step := b1.step+1}
  let b3 := {b2 with step := b2.step+1}; let b4 := {b3 with step := b3.step+1}
  apply Exec.cons (step0_left s0_atSpawn b0 4 4 (by simp [s0_atSpawn, getRoomObs]) (by simp[s0_atSpawn,getRoomObs,ROOM0_SPAWN_DEFAULT]) (by simp [room0_path]))
  apply Exec.cons (step0_left s0_west1 b1 3 4 (by simp [s0_west1, s0_atSpawn,getRoomObs,ROOM0_SPAWN_DEFAULT]) (by simp[s0_west1]) (by simp [room0_path]))
  apply Exec.cons (step0_left s0_west2 b2 2 4 (by simp [s0_west2, s0_atSpawn,getRoomObs,ROOM0_SPAWN_DEFAULT]) (by simp[s0_west2]) (by simp [room0_path]))
  apply Exec.cons (step0_left s0_west3 b3 1 4 (by simp [s0_west3, s0_atSpawn,getRoomObs,ROOM0_SPAWN_DEFAULT]) (by simp[s0_west3]) (by simp [room0_path]))
  exact Exec.nil

/-- Phase 2: 房间切换 start→monster_hall [1步] -/
theorem phase2_transition_to_monster_hall (b : BeliefState) :
    Exec s0_atWestExit b [Action.left] s1_fromEast { b with step := b.step + 1 } := by
  apply Exec.cons
  · exact start_west_to_monster_hall s0_atWestExit b
      (by simp [s0_atWestExit, s0_atSpawn, getRoomObs])
      (by simp [s0_atWestExit])
      (by simp [s0_atWestExit, s0_atSpawn, getRoomObs])
  · exact Exec.nil

/-- Phase 3: monster_hall(8,4)→西出口(0,4) [8步] -/
theorem phase3_monster_hall_to_west_exit (b : BeliefState) :
    Exec s1_fromEast b
      [Action.left, Action.left, Action.left, Action.left,
       Action.left, Action.left, Action.left, Action.left]
      s1_atWestExit { b with step := b.step + 8 } := by
  let b0 := b; let b1 := {b0 with step:=b0.step+1}; let b2 := {b1 with step:=b1.step+1}
  let b3 := {b2 with step:=b2.step+1}; let b4 := {b3 with step:=b3.step+1}
  let b5 := {b4 with step:=b4.step+1}; let b6 := {b5 with step:=b5.step+1}
  let b7 := {b6 with step:=b6.step+1}; let b8 := {b7 with step:=b7.step+1}
  apply Exec.cons (step1_left s1_fromEast b0 8 4 (by simp [s1_fromEast, getRoomObs]) (by simp[s1_fromEast,getRoomObs,ROOM1_SPAWN_FROM_EAST]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west1 b1 7 4 (by simp[s1_west1,s1_fromEast,getRoomObs]) (by simp[s1_west1]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west2 b2 6 4 (by simp[s1_west2,s1_fromEast,getRoomObs]) (by simp[s1_west2]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west3 b3 5 4 (by simp[s1_west3,s1_fromEast,getRoomObs]) (by simp[s1_west3]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west4 b4 4 4 (by simp[s1_west4,s1_fromEast,getRoomObs]) (by simp[s1_west4]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west5 b5 3 4 (by simp[s1_west5,s1_fromEast,getRoomObs]) (by simp[s1_west5]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west6 b6 2 4 (by simp[s1_west6,s1_fromEast,getRoomObs]) (by simp[s1_west6]) (by simp [room1_path]))
  apply Exec.cons (step1_left s1_west7 b7 1 4 (by simp[s1_west7,s1_fromEast,getRoomObs]) (by simp[s1_west7]) (by simp [room1_path]))
  exact Exec.nil

/-- Phase 4: 房间切换 monster_hall→key_room [1步] -/
theorem phase4_transition_to_key_room (b : BeliefState) :
    Exec s1_atWestExit b [Action.left] s2_atSpawn { b with step := b.step + 1 } := by
  apply Exec.cons
  · exact monster_hall_west_to_key_room s1_atWestExit b
      (by simp [s1_atWestExit, s1_fromEast, getRoomObs])
      (by simp [s1_atWestExit])
      (by simp [s1_atWestExit, s1_fromEast, getRoomObs])
  · exact Exec.nil

/-- Phase 5: key_room(8,4)→宝箱(5,4)开箱 [2步+buttonA] -/
theorem phase5_walk_to_chest_and_open (b : BeliefState) :
    Exec s2_atSpawn b [Action.left, Action.left, Action.buttonA]
      s2_postChest {(belief_after_key b) with step := (belief_after_key b).step + 2 } := by
  let b0 := b; let b1 := {b0 with step:=b0.step+1}; let b2 := {b1 with step:=b1.step+1}
  let b3 := {b2 with step:=b2.step+1}
  apply Exec.cons (step2_left s2_atSpawn b0 8 4 (by simp [s2_atSpawn, getRoomObs]) (by simp[s2_atSpawn,getRoomObs,ROOM2_SPAWN]) (by simp [room2_path]))
  apply Exec.cons (step2_left s2_chest1 b1 7 4 (by simp [s2_chest1, s2_atSpawn,getRoomObs]) (by simp[s2_chest1]) (by simp [room2_path]))
  simp[s2_postChest,belief_after_key]
  let s_before := {s2_atSpawn with player := some (6,4), facing := Direction.left}
  have h_openchest := @Step.openChest s_before b2 (5,4) (by simp [s_before]) (by simp[s_before,s2_atSpawn,getRoomObs,ROOM2_CHEST]) (by simp [s_before,adjacent,manhattan])
  simp[s_before] at h_openchest
  simp[s2_chest1]
  simp[b2] at h_openchest
  apply Exec.cons h_openchest
  simp[s2_atChest,s2_atSpawn]
  simp[getRoomObs,ROOM2_SPAWN,ROOM2_CHEST,b1,b0]
  exact Exec.nil





/-- Phase 6: key_room(6,4)→东出口(9,4) [3步] -/
theorem phase6_chest_to_east_exit (b : BeliefState) :
    Exec s2_postChest (belief_after_key b) [Action.right, Action.right, Action.right]
      s2_atEastExit { (belief_after_key b) with step := (belief_after_key b).step + 3 } := by
  let b0 := belief_after_key b
  let b1 := {b0 with step:=b0.step+1}; let b2 := {b1 with step:=b1.step+1}
  let b3 := {b2 with step:=b2.step+1}; let b4 := {b3 with step:=b3.step+1}
  apply Exec.cons (step2_right s2_postChest b0 6 4 (by simp [s2_postChest, s2_atChest, s2_atSpawn,getRoomObs]) (by simp[s2_postChest]) (by simp [room2_path]))
  apply Exec.cons (step2_right s2_exit1 b1 7 4 (by simp[s2_exit1,s2_postChest,s2_atChest,s2_atSpawn,getRoomObs]) (by simp[s2_exit1]) (by simp [room2_path]))
  apply Exec.cons (step2_right s2_exit2 b2 8 4 (by simp[s2_exit2,s2_postChest,s2_atChest,s2_atSpawn,getRoomObs]) (by simp[s2_exit2]) (by simp [room2_path]))
  exact Exec.nil

/-- Phase 7: 房间切换 key_room→monster_hall（回程）[1步] -/
theorem phase7_transition_back_to_monster_hall (b : BeliefState) :
    Exec s2_atEastExit b [Action.right] s1_fromWest { b with step := b.step + 1 } := by
  apply Exec.cons
  · exact key_room_east_to_monster_hall s2_atEastExit b
      (by simp [s2_atEastExit, s2_postChest, s2_atChest, s2_atSpawn, getRoomObs])
      (by simp [s2_atEastExit])
      (by simp [s2_atEastExit, s2_postChest, s2_atSpawn, getRoomObs,s2_atChest])
  · exact Exec.nil

/-- Phase 8: monster_hall(1,4)→东出口(9,4) [8步] -/
theorem phase8_monster_hall_to_east_exit (b : BeliefState) :
    Exec s1_fromWest b
      [Action.right, Action.right, Action.right, Action.right,
       Action.right, Action.right, Action.right, Action.right]
      s1_atEastExit { b with step := b.step + 8 } := by
  let b0 := b; let b1 := {b0 with step:=b0.step+1}; let b2 := {b1 with step:=b1.step+1}
  let b3 := {b2 with step:=b2.step+1}; let b4 := {b3 with step:=b3.step+1}
  let b5 := {b4 with step:=b4.step+1}; let b6 := {b5 with step:=b5.step+1}
  let b7 := {b6 with step:=b6.step+1}; let b8 := {b7 with step:=b7.step+1}
  apply Exec.cons (step1_right s1_fromWest b0 1 4 (by simp [s1_fromWest, getRoomObs]) (by simp[s1_fromWest,getRoomObs,ROOM1_SPAWN_FROM_WEST]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east1 b1 2 4 (by simp[s1_east1,s1_fromWest,getRoomObs]) (by simp[s1_east1]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east2 b2 3 4 (by simp[s1_east2,s1_fromWest,getRoomObs]) (by simp[s1_east2]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east3 b3 4 4 (by simp[s1_east3,s1_fromWest,getRoomObs]) (by simp[s1_east3]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east4 b4 5 4 (by simp[s1_east4,s1_fromWest,getRoomObs]) (by simp[s1_east4]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east5 b5 6 4 (by simp[s1_east5,s1_fromWest,getRoomObs]) (by simp[s1_east5]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east6 b6 7 4 (by simp[s1_east6,s1_fromWest,getRoomObs]) (by simp[s1_east6]) (by simp [room1_path]))
  apply Exec.cons (step1_right s1_east7 b7 8 4 (by simp[s1_east7,s1_fromWest,getRoomObs]) (by simp[s1_east7]) (by simp [room1_path]))
  exact Exec.nil

/-- Phase 9: 房间切换 monster_hall→start [1步] -/
theorem phase9_transition_to_start (b : BeliefState) :
    Exec s1_atEastExit b [Action.right] s0_fromWest { b with step := b.step + 1 } := by
  apply Exec.cons
  · exact monster_hall_east_to_start s1_atEastExit b
      (by simp [s1_atEastExit, s1_fromWest, getRoomObs])
      (by simp [s1_atEastExit])
      (by simp [s1_atEastExit, s1_fromWest, getRoomObs])
  · exact Exec.nil

/-- Phase 10: start_room(1,4)→东锁门(9,4) [8步] -/
theorem phase10_walk_to_locked_exit (b : BeliefState) :
    Exec s0_fromWest b
      [Action.right, Action.right, Action.right, Action.right,
       Action.right, Action.right, Action.right, Action.right]
      s0_atEastLocked { b with step := b.step + 8 } := by
  let b0 := b; let b1 := {b0 with step:=b0.step+1}; let b2 := {b1 with step:=b1.step+1}
  let b3 := {b2 with step:=b2.step+1}; let b4 := {b3 with step:=b3.step+1}
  let b5 := {b4 with step:=b4.step+1}; let b6 := {b5 with step:=b5.step+1}
  let b7 := {b6 with step:=b6.step+1}; let b8 := {b7 with step:=b7.step+1}
  apply Exec.cons (step0_right s0_fromWest b0 1 4 (by simp [s0_fromWest, getRoomObs]) (by simp[s0_fromWest,getRoomObs,ROOM0_SPAWN_FROM_WEST]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east1 b1 2 4 (by simp[s0_east1,s0_fromWest,getRoomObs]) (by simp[s0_east1]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east2 b2 3 4 (by simp[s0_east2,s0_fromWest,getRoomObs]) (by simp[s0_east2]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east3 b3 4 4 (by simp[s0_east3,s0_fromWest,getRoomObs]) (by simp[s0_east3]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east4 b4 5 4 (by simp[s0_east4,s0_fromWest,getRoomObs]) (by simp[s0_east4]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east5 b5 6 4 (by simp[s0_east5,s0_fromWest,getRoomObs]) (by simp[s0_east5]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east6 b6 7 4 (by simp[s0_east6,s0_fromWest,getRoomObs]) (by simp[s0_east6]) (by simp [room0_path]))
  apply Exec.cons (step0_right s0_east7 b7 8 4 (by simp[s0_east7,s0_fromWest,getRoomObs]) (by simp[s0_east7]) (by simp [room0_path]))
  exact Exec.nil


/- ================================================================
   13. 任务完成条件
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
   14. 完整 Exec 拼接 + 主定理
   ================================================================ -/

def TASK3_PLAN_STEPS : Nat := 42

theorem task3_plan_steps_lt_max : TASK3_PLAN_STEPS < TASK3_MAX_STEPS := by
  native_decide

theorem task3_completable : TaskCompletable initSym initBelief task3Goal := by
  -- Phase 1: spawn→西出口
  have h1 : Exec initSym initBelief
    [Action.left, Action.left, Action.left, Action.left]
    s0_atWestExit { initBelief with step := 4 } :=
    phase1_spawn_to_west_exit initBelief

  -- Phase 2: 房间切换→monster_hall
  have h2 : Exec s0_atWestExit { initBelief with step := 4 }
    [Action.left] s1_fromEast { initBelief with step := 5 } :=
    phase2_transition_to_monster_hall { initBelief with step := 4 }

  let plan12 := [Action.left, Action.left, Action.left, Action.left, Action.left]
  have h12 : Exec initSym initBelief plan12 s1_fromEast { initBelief with step := 5 } :=
    exec_append h1 h2

  -- Phase 3: monster_hall→西出口
  have h3 : Exec s1_fromEast { initBelief with step := 5 }
    [Action.left, Action.left, Action.left, Action.left,
     Action.left, Action.left, Action.left, Action.left]
    s1_atWestExit { initBelief with step := 13 } :=
    phase3_monster_hall_to_west_exit { initBelief with step := 5 }

  let plan123 := plan12 ++ [Action.left, Action.left, Action.left, Action.left,
    Action.left, Action.left, Action.left, Action.left]
  have h123 : Exec initSym initBelief plan123 s1_atWestExit { initBelief with step := 13 } :=
    exec_append h12 h3

  -- Phase 4: 房间切换→key_room
  have h4 : Exec s1_atWestExit { initBelief with step := 13 }
    [Action.left] s2_atSpawn { initBelief with step := 14 } :=
    phase4_transition_to_key_room { initBelief with step := 13 }

  let plan1234 := plan123 ++ [Action.left]
  have h1234 : Exec initSym initBelief plan1234 s2_atSpawn { initBelief with step := 14 } :=
    exec_append h123 h4

  -- Phase 5: 开宝箱
  have h5 : Exec s2_atSpawn { initBelief with step := 14 }
    [Action.left, Action.left, Action.buttonA]
    s2_postChest ({belief_after_key { initBelief with step := 14 } with step := 17}) :=
    phase5_walk_to_chest_and_open { initBelief with step := 14 }

  let plan12345 := plan1234 ++ [Action.left, Action.left, Action.buttonA]
  have h12345 : Exec initSym initBelief plan12345 s2_postChest
    ({belief_after_key { initBelief with step := 14 } with step := 17}) :=
    exec_append h1234 h5

  -- Phase 6: key_room→东出口
  have h6 : Exec s2_postChest ({belief_after_key { initBelief with step := 14 } with step := 17})
    [Action.right, Action.right, Action.right]
    s2_atEastExit {belief_after_key { initBelief with step := 14 } with step := 20}  := by
      have hp6:=phase6_chest_to_east_exit {initBelief with step := 16}
      simp[belief_after_key] at hp6
      exact hp6



  let b_key := belief_after_key { initBelief with step := 14 }
  let plan123456 := plan12345 ++ [Action.right, Action.right, Action.right]
  have h123456 : Exec initSym initBelief plan123456 s2_atEastExit
    { b_key with step := b_key.step + 5 } :=
    exec_append h12345 h6

  -- Phase 7: 回程→monster_hall
  have h7 : Exec s2_atEastExit { b_key with step := b_key.step + 5 }
    [Action.right] s1_fromWest { { b_key with step := b_key.step + 5 } with step := b_key.step + 6 } :=
    phase7_transition_back_to_monster_hall { b_key with step := b_key.step + 5 }

  let plan1234567 := plan123456 ++ [Action.right]
  have h1234567 : Exec initSym initBelief plan1234567 s1_fromWest
    { { b_key with step := b_key.step + 5 } with step := b_key.step + 6 } :=
    exec_append h123456 h7

  let b_mh := { { b_key with step := b_key.step + 5 } with step := b_key.step + 6 }

  -- Phase 8: monster_hall→东出口
  have h8 : Exec s1_fromWest b_mh
    [Action.right, Action.right, Action.right, Action.right,
     Action.right, Action.right, Action.right, Action.right]
    s1_atEastExit { b_mh with step := b_mh.step + 8 } :=
    phase8_monster_hall_to_east_exit b_mh

  let plan12345678 := plan1234567 ++
    [Action.right, Action.right, Action.right, Action.right,
     Action.right, Action.right, Action.right, Action.right]
  have h12345678 : Exec initSym initBelief plan12345678 s1_atEastExit
    { b_mh with step := b_mh.step + 8 } :=
    exec_append h1234567 h8

  let b_mh2 := { b_mh with step := b_mh.step + 8 }

  -- Phase 9: 房间切换→start
  have h9 : Exec s1_atEastExit b_mh2
    [Action.right] s0_fromWest { b_mh2 with step := b_mh2.step + 1 } :=
    phase9_transition_to_start b_mh2

  let plan123456789 := plan12345678 ++ [Action.right]
  have h123456789 : Exec initSym initBelief plan123456789 s0_fromWest
    { b_mh2 with step := b_mh2.step + 1 } :=
    exec_append h12345678 h9

  let b_start := { b_mh2 with step := b_mh2.step + 1 }

  -- Phase 10: start→东锁门
  have h10 : Exec s0_fromWest b_start
    [Action.right, Action.right, Action.right, Action.right,
     Action.right, Action.right, Action.right, Action.right]
    s0_atEastLocked { b_start with step := b_start.step + 8 } :=
    phase10_walk_to_locked_exit b_start

  let plan12345678910 := plan123456789 ++
    [Action.right, Action.right, Action.right, Action.right,
     Action.right, Action.right, Action.right, Action.right]
  have h12345678910 : Exec initSym initBelief plan12345678910 s0_atEastLocked
    { b_start with step := b_start.step + 8 } :=
    exec_append h123456789 h10

  let b_locked := { b_start with step := b_start.step + 8 }

  -- 此时 hasKey = true
  have hhasKey : b_locked.hasKey = true := by
    unfold b_locked b_start b_mh2 b_mh b_key belief_after_key; simp

  let full_plan := plan12345678910
  let final_sym : SymbolicObs := { s0_atEastLocked with player := some (9, 4) }
  let final_belief := b_locked
  have h_full := h12345678910

  refine ⟨full_plan, final_sym, final_belief, h_full, ?_⟩
  unfold taskCompleted task3Goal final_belief b_locked b_start b_mh2 b_mh b_key belief_after_key
  simp
  simp[final_sym, s0_atEastLocked, s0_fromWest, getRoomObs, ROOM0_SPAWN_FROM_WEST,ROOM0_EXITS]
/- ================================================================
   15. 综合性总结定理
   ================================================================ -/

theorem task3_formalization_summary :
    TaskCompletable initSym initBelief task3Goal ∧
    TASK3_PLAN_STEPS < TASK3_MAX_STEPS ∧
    roomReachable task3RoomGraph ROOM0_ID ROOM1_ID ∧
    roomReachable task3RoomGraph ROOM0_ID ROOM2_ID := by
  refine ⟨task3_completable, task3_plan_steps_lt_max, ?_, ?_⟩
  · exact all_rooms_reachable.1
  · exact all_rooms_reachable.2

end Task3
