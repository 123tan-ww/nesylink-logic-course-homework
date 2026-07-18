/-
  Task4Formalization.lean

  对应关卡 mathematical_logic/task_4：
  - 5 个房间：west(-1,0), center(0,0), north(0,-1), east(1,0), south(0,1)
  - 玩家初始无剑（只有盾）
  - center 房间有 rotating_bridge，3 种状态（由 west 的 switch 控制）
  - north 房间有宝箱（含钥匙）
  - east 房间有宝箱（含剑），需钥匙开门（不消耗钥匙）
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
   0. 任务常量
   ================================================================ -/

def TASK4_MAX_STEPS : Nat := 2000

/- ================================================================
   1. 房间 ID
   ================================================================ -/

def ROOM_WEST   : RoomId := 0
def ROOM_CENTER : RoomId := 1
def ROOM_NORTH  : RoomId := 2
def ROOM_EAST   : RoomId := 3
def ROOM_SOUTH  : RoomId := 4

/- ================================================================
   2. 桥状态 — Task 4 特有的动态对象
   ================================================================ -/

inductive BridgeState where
  | westToNorth   -- 初始：west↔center + center↔north
  | westToEast    -- 切换后：west↔center + center↔east
  | westToSouth   -- 切换后：west↔center + center↔south
  deriving DecidableEq, Repr

/-- 桥状态循环顺序 -/
def nextBridgeState (s : BridgeState) : BridgeState :=
  match s with
  | BridgeState.westToNorth => BridgeState.westToEast
  | BridgeState.westToEast  => BridgeState.westToSouth
  | BridgeState.westToSouth => BridgeState.westToNorth

/-- 桥的 3 种状态对应的可通行 tile 集合 -/
def bridgeTiles (state : BridgeState) : List Position :=
  match state with
  | BridgeState.westToNorth =>
    [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),
     (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),
     (4,0),(5,0),(4,1),(5,1),(4,2),(5,2)]
  | BridgeState.westToEast =>
    [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,3),(7,3),(8,3),(9,3),
     (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(7,4),(8,4),(9,4)]
  | BridgeState.westToSouth =>
    [(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),
     (0,4),(1,4),(2,4),(3,4),(4,4),(5,4),
     (4,5),(5,5),(4,6),(5,6),(4,7),(5,7)]

/- ================================================================
   3. 地图常量 — 五个房间
   ================================================================ -/

/-- west（起点 [-1,0]）：四周有墙，中间两行开口 -/
def WEST_WALLS : List Position :=
  [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0),(9,0),
   (0,1),(9,1),(0,2),(9,2),(0,5),(9,5),(0,6),(9,6),
   (0,7),(1,7),(2,7),(3,7),(4,7),(5,7),(6,7),(7,7),(8,7),(9,7)]
def WEST_SWITCH : Position := (4, 4)
def WEST_EXIT_EAST : Position := (9, 4)
def WEST_SPAWN : Position := (7, 4)

/-- center（中心 [0,0]）：所有 tile 为深渊，桥面覆盖部分区域 -/
def CENTER_EXIT_WEST  : Position := (0, 4)
def CENTER_EXIT_EAST  : Position := (9, 4)
def CENTER_EXIT_NORTH : Position := (4, 0)
def CENTER_EXIT_SOUTH : Position := (4, 7)
def CENTER_SPAWN_FROM_WEST  : Position := (1, 4)
def CENTER_SPAWN_FROM_EAST  : Position := (8, 4)
def CENTER_SPAWN_FROM_NORTH : Position := (4, 1)
def CENTER_SPAWN_FROM_SOUTH : Position := (4, 6)
def CENTER_FINAL_CHEST : Position := (4, 4)

/-- north（北 [0,-1]）：有墙，底部通 center -/
def NORTH_WALLS : List Position :=
  [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0),(9,0),
   (0,1),(9,1),(0,2),(9,2),(0,3),(9,3),
   (0,4),(9,4),(0,5),(9,5),(0,6),(9,6),
   (0,7),(1,7),(2,7),(3,7),(6,7),(7,7),(8,7),(9,7)]
def NORTH_CHEST : Position := (4, 3)
def NORTH_EXIT_SOUTH : Position := (4, 7)
def NORTH_SPAWN : Position := (4, 1)

/-- east（东 [1,0]）：有墙，中间两行开口 -/
def EAST_WALLS : List Position := WEST_WALLS
def EAST_CHEST : Position := (5, 4)
def EAST_EXIT_WEST : Position := (0, 4)
def EAST_SPAWN : Position := (1, 4)

/-- south（南 [0,1]）：有墙，顶部通 center -/
def SOUTH_WALLS : List Position :=
  [(0,0),(1,0),(2,0),(3,0),(6,0),(7,0),(8,0),(9,0),
   (0,1),(9,1),(0,2),(9,2),(0,3),(9,3),
   (0,4),(9,4),(0,5),(9,5),(0,6),(9,6),
   (0,7),(1,7),(2,7),(3,7),(4,7),(5,7),(6,7),(7,7),(8,7),(9,7)]
def SOUTH_MONSTER : Position := (4, 4)
def SOUTH_EXIT_NORTH : Position := (4, 0)
def SOUTH_SPAWN : Position := (4, 6)

/- ================================================================
   4. 网格构造
   ================================================================ -/

def buildWestGrid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ WEST_WALLS then TILE_WALL
      else if (x, y) = WEST_EXIT_EAST then TILE_EXIT
      else if (x, y) = WEST_SWITCH then TILE_SWITCH
      else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

/-- center 网格根据桥状态动态生成（深渊 + 桥面）-/
def buildCenterGrid (bs : BridgeState) : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ [CENTER_EXIT_WEST, CENTER_EXIT_EAST, CENTER_EXIT_NORTH, CENTER_EXIT_SOUTH] then TILE_EXIT
      else if (x, y) ∈ bridgeTiles bs then TILE_BRIDGE
      else TILE_GAP)
    (List.range ROOM_W))
  (List.range ROOM_H)

def buildNorthGrid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ NORTH_WALLS then TILE_WALL
      else if (x, y) = NORTH_CHEST then TILE_CHEST
      else if (x, y) = NORTH_EXIT_SOUTH then TILE_EXIT
      else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

def buildEastGrid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ EAST_WALLS then TILE_WALL
      else if (x, y) = EAST_CHEST then TILE_CHEST
      else if (x, y) = EAST_EXIT_WEST then TILE_EXIT
      else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

def buildSouthGrid : Grid :=
  List.map (fun (y : Nat) =>
    List.map (fun (x : Nat) =>
      if (x, y) ∈ SOUTH_WALLS then TILE_WALL
      else if (x, y) = SOUTH_EXIT_NORTH then TILE_EXIT
      else TILE_EMPTY)
    (List.range ROOM_W))
  (List.range ROOM_H)

/- ================================================================
   5. 初始状态 — 从 west 出发
   ================================================================ -/

def initSym : SymbolicObs :=
  { player := some WEST_SPAWN
    facing := Direction.down
    monsters := []
    chests := []
    exits := [WEST_EXIT_EAST]
    traps := []
    buttons := []
    switches := [WEST_SWITCH]
    grid := buildWestGrid
  }

def initBelief : BeliefState :=
  { hasKey := false, hasSword := false, keys := 0, gold := 0,
    openedChests := [], killedMonsters := [], pressedButtons := [], step := 0
  }

/-- 初始扩展状态（含桥和剑状态）-/
structure Task4SymbolicObs where
  toSymbolicObs : SymbolicObs
  bridgeState : BridgeState
  hasSword : Bool

def initSym4 : Task4SymbolicObs :=
  { toSymbolicObs := initSym, bridgeState := BridgeState.westToNorth, hasSword := false }
/- ================================================================
   6. 房间状态构造器 + 出口→目标映射
   ================================================================ -/

/-- 根据 roomId 和桥状态构造房间符号状态 -/
def getRoomObs (rid : RoomId) (playerPos : Position) (bs : BridgeState) : Task4SymbolicObs :=
  match rid with
  | 0 => { toSymbolicObs :=
           { player := some playerPos, facing := Direction.down,
             monsters := [], chests := [], exits := [WEST_EXIT_EAST],
             traps := [], buttons := [], switches := [WEST_SWITCH],
             grid := buildWestGrid }
           bridgeState := bs, hasSword := false }
  | 1 => { toSymbolicObs :=
           { player := some playerPos, facing := Direction.down,
             monsters := [], chests := [],
             exits := [CENTER_EXIT_WEST, CENTER_EXIT_EAST, CENTER_EXIT_NORTH, CENTER_EXIT_SOUTH],
             traps := [], buttons := [], switches := [],
             grid := buildCenterGrid bs }
           bridgeState := bs, hasSword := false }
  | 2 => { toSymbolicObs :=
           { player := some playerPos, facing := Direction.down,
             monsters := [], chests := [NORTH_CHEST],
             exits := [NORTH_EXIT_SOUTH],
             traps := [], buttons := [], switches := [],
             grid := buildNorthGrid }
           bridgeState := bs, hasSword := false }
  | 3 => { toSymbolicObs :=
           { player := some playerPos, facing := Direction.down,
             monsters := [], chests := [EAST_CHEST],
             exits := [EAST_EXIT_WEST],
             traps := [], buttons := [], switches := [],
             grid := buildEastGrid }
           bridgeState := bs, hasSword := false }
  | 4 => { toSymbolicObs :=
           { player := some playerPos, facing := Direction.down,
             monsters := [SOUTH_MONSTER], chests := [],
             exits := [SOUTH_EXIT_NORTH],
             traps := [], buttons := [], switches := [],
             grid := buildSouthGrid }
           bridgeState := bs, hasSword := false }
  | _  => initSym4

/-- 从 (当前房间, 出口坐标) 映射到 (目标房间, 出生点) -/
def exitToDest (rid : RoomId) (exitPos : Position) : Option (RoomId × Position) :=
  match rid, exitPos with
  | 0, (9, 4) => some (1, CENTER_SPAWN_FROM_WEST)   -- west→center
  | 1, (0, 4) => some (0, WEST_SPAWN)                -- center→west
  | 1, (9, 4) => some (3, EAST_SPAWN)                -- center→east（锁门）
  | 1, (4, 0) => some (2, NORTH_SPAWN)               -- center→north
  | 1, (4, 7) => some (4, SOUTH_SPAWN)               -- center→south
  | 2, (4, 7) => some (1, CENTER_SPAWN_FROM_NORTH)   -- north→center
  | 3, (0, 4) => some (1, CENTER_SPAWN_FROM_EAST)    -- east→center
  | 4, (4, 0) => some (1, CENTER_SPAWN_FROM_SOUTH)   -- south→center
  | _, _      => none

/- ================================================================
   7. 房间图
   ================================================================ -/

def task4RoomGraph : RoomGraph :=
  {
    roomId2Coord := [
      (ROOM_WEST,   { x := -1, y := 0 }),
      (ROOM_CENTER, { x := 0,  y := 0 }),
      (ROOM_NORTH,  { x := 0,  y := -1 }),
      (ROOM_EAST,   { x := 1,  y := 0 }),
      (ROOM_SOUTH,  { x := 0,  y := 1 })
    ]
    roomCoord2Id := [
      ({ x := -1, y := 0 }, ROOM_WEST),
      ({ x := 0,  y := 0 }, ROOM_CENTER),
      ({ x := 0,  y := -1 }, ROOM_NORTH),
      ({ x := 1,  y := 0 }, ROOM_EAST),
      ({ x := 0,  y := 1 }, ROOM_SOUTH)
    ]
    roomExits := [
      (0, [("east", { direction := "east", exitType := "normal", opened := true,
                      dest := 1, start := 0, tiles := [(9,4)], isReached := false })]),
      (1, [("west",  { direction := "west",  exitType := "normal",     opened := true,  dest := 0, start := 1, tiles := [(0,4)], isReached := false }),
           ("east",  { direction := "east",  exitType := "locked_key", opened := false, dest := 3, start := 1, tiles := [(9,4)], isReached := false }),
           ("north", { direction := "north", exitType := "normal",     opened := true,  dest := 2, start := 1, tiles := [(4,0)], isReached := false }),
           ("south", { direction := "south", exitType := "normal",     opened := true,  dest := 4, start := 1, tiles := [(4,7)], isReached := false })]),
      (2, [("south", { direction := "south", exitType := "normal", opened := true,
                       dest := 1, start := 2, tiles := [(4,7)], isReached := false })]),
      (3, [("west",  { direction := "west",  exitType := "normal", opened := true,
                       dest := 1, start := 3, tiles := [(0,4)], isReached := false })]),
      (4, [("north", { direction := "north", exitType := "normal", opened := true,
                       dest := 1, start := 4, tiles := [(4,0)], isReached := false })])
    ]
  }

/- ================================================================
   8. 房间间可达性
   ================================================================ -/

theorem west_to_north_reachable :
    roomReachable task4RoomGraph ROOM_WEST ROOM_NORTH := by
  simp[roomReachable]
  have h1: adjacentRooms task4RoomGraph ROOM_WEST ROOM_CENTER := by
    unfold adjacentRooms; simp [task4RoomGraph]
    exists "east", { direction := "east", exitType := "normal", opened := true,dest := 1, start := 0, tiles := [(9,4)], isReached := false }
  have h2: adjacentRooms task4RoomGraph ROOM_CENTER ROOM_NORTH := by
    unfold adjacentRooms; simp [task4RoomGraph]
    exists "north", { direction := "north", exitType := "normal", opened := true,dest := 2, start := 1, tiles := [(4,0)], isReached := false }
  exact RoomPath.step h1 (RoomPath.step h2 RoomPath.self)

theorem west_to_east_reachable :
    roomReachable task4RoomGraph ROOM_WEST ROOM_EAST := by
  simp[roomReachable]
  have h1: adjacentRooms task4RoomGraph ROOM_WEST ROOM_CENTER := by
    unfold adjacentRooms; simp [task4RoomGraph]
    exists "east", { direction := "east", exitType := "normal", opened := true,dest := 1, start := 0, tiles := [(9,4)], isReached := false }
  have h2: adjacentRooms task4RoomGraph ROOM_CENTER ROOM_EAST := by
    unfold adjacentRooms; simp [task4RoomGraph]
    exists "east",  { direction := "east",  exitType := "locked_key", opened := false, dest := 3, start := 1, tiles := [(9,4)], isReached := false }
  exact RoomPath.step h1 (RoomPath.step h2 RoomPath.self)

theorem west_to_south_reachable :
    roomReachable task4RoomGraph ROOM_WEST ROOM_SOUTH := by
  simp[roomReachable]
  have h1: adjacentRooms task4RoomGraph ROOM_WEST ROOM_CENTER := by
    unfold adjacentRooms; simp [task4RoomGraph]
    exists "east", { direction := "east", exitType := "normal", opened := true,dest := 1, start := 0, tiles := [(9,4)], isReached := false }
  have h2: adjacentRooms task4RoomGraph ROOM_CENTER ROOM_SOUTH := by
    unfold adjacentRooms; simp [task4RoomGraph]
    exists "south", { direction := "south", exitType := "normal",     opened := true,  dest := 4, start := 1, tiles := [(4,7)], isReached := false }
  exact RoomPath.step h1 (RoomPath.step h2 RoomPath.self)

theorem all_rooms_reachable :
    roomReachable task4RoomGraph ROOM_WEST ROOM_NORTH ∧
    roomReachable task4RoomGraph ROOM_WEST ROOM_EAST ∧
    roomReachable task4RoomGraph ROOM_WEST ROOM_SOUTH := by
  refine ⟨west_to_north_reachable, west_to_east_reachable, west_to_south_reachable⟩

/- ================================================================
   9. 房间切换定理
   ================================================================ -/

theorem west_east_to_center (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildWestGrid) (hplayer : s.player = some (9, 4))
    (hexits : s.exits = [WEST_EXIT_EAST]) :
    Step s b Action.right (getRoomObs 1 CENTER_SPAWN_FROM_WEST bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 1 CENTER_SPAWN_FROM_WEST bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.right := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.right s.exits := by
    simp [hplayer, hexits, WEST_EXIT_EAST, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildCenterGrid bs := by simp [room', getRoomObs]
    have h1 : s.grid = buildWestGrid := hgrid
    rw [h0, h1] at h_eq
    have : buildCenterGrid bs ≠ buildWestGrid := by
      simp[buildCenterGrid,buildWestGrid];exists 0;simp[ROOM_H,ROOM_W];exists 4;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; unfold buildCenterGrid; simp [bridgeTiles]
    simp [isSafeMoveB,CENTER_SPAWN_FROM_WEST,inBoundsB,isBlockedB,ROOM_W,ROOM_H,getTile,CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH,TILE_WALL,TILE_BRIDGE,TILE_BRIDGE,TILE_GAP,TILE_TRAP,TILE_CHEST,TILE_EXIT,TILE_MONSTER]
    match bs with
    | BridgeState.westToNorth => simp
    | BridgeState.westToEast  => simp
    | BridgeState.westToSouth => simp

  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem center_west_to_west (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildCenterGrid bs) (hplayer : s.player = some (0, 4))
    (hexits : s.exits = [CENTER_EXIT_WEST, CENTER_EXIT_EAST, CENTER_EXIT_NORTH, CENTER_EXIT_SOUTH]) :
    Step s b Action.left (getRoomObs 0 WEST_SPAWN bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 0 WEST_SPAWN bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.left := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.left s.exits := by
    simp [hplayer, hexits, CENTER_EXIT_WEST, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildWestGrid := by simp [room', getRoomObs]
    have h1 : s.grid = buildCenterGrid bs := hgrid
    rw [h0, h1] at h_eq
    have : buildWestGrid ≠ buildCenterGrid bs := by
      simp[buildCenterGrid,buildWestGrid];exists 0;simp[ROOM_H,ROOM_W];exists 4;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem center_north_to_north (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildCenterGrid bs) (hplayer : s.player = some (4, 0))
    (hexits : s.exits = [CENTER_EXIT_WEST, CENTER_EXIT_EAST, CENTER_EXIT_NORTH, CENTER_EXIT_SOUTH]) :
    Step s b Action.up (getRoomObs 2 NORTH_SPAWN bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 2 NORTH_SPAWN bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.up := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.up s.exits := by
    simp [hplayer, hexits, CENTER_EXIT_NORTH, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildNorthGrid := by simp [room', getRoomObs]
    have h1 : s.grid = buildCenterGrid bs := hgrid
    rw [h0, h1] at h_eq
    have : buildNorthGrid ≠ buildCenterGrid bs := by
      simp[buildCenterGrid,buildNorthGrid];exists 0;simp[ROOM_H,ROOM_W];exists 4;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem north_south_to_center (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildNorthGrid) (hplayer : s.player = some (4, 7))
    (hexits : s.exits = [NORTH_EXIT_SOUTH]) (hbs : bs = BridgeState.westToNorth):
    Step s b Action.down (getRoomObs 1 CENTER_SPAWN_FROM_NORTH bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 1 CENTER_SPAWN_FROM_NORTH bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.down := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.down s.exits := by
    simp [hplayer, hexits, NORTH_EXIT_SOUTH, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildCenterGrid bs := by simp [room', getRoomObs]
    have h1 : s.grid = buildNorthGrid := hgrid
    rw [h0, h1] at h_eq
    have : buildCenterGrid bs ≠ buildNorthGrid := by
      simp[buildCenterGrid,buildNorthGrid];exists 0;simp[ROOM_H,ROOM_W];exists 4;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; unfold buildCenterGrid; simp [bridgeTiles]
    simp [isSafeMoveB,CENTER_SPAWN_FROM_NORTH,inBoundsB,isBlockedB,ROOM_W,ROOM_H,getTile,CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH,TILE_WALL,TILE_BRIDGE,TILE_BRIDGE,TILE_GAP,TILE_TRAP,TILE_CHEST,TILE_EXIT,TILE_MONSTER]
    rw[hbs];simp
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem center_east_to_east_locked (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildCenterGrid bs) (hplayer : s.player = some (9, 4))
    (hexits : s.exits = [CENTER_EXIT_WEST, CENTER_EXIT_EAST, CENTER_EXIT_NORTH, CENTER_EXIT_SOUTH])
    (hhasKey : b.hasKey = true) :
    Step s b Action.right (getRoomObs 3 EAST_SPAWN bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 3 EAST_SPAWN bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.right := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.right s.exits := by
    simp [hplayer, hexits, CENTER_EXIT_EAST, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildEastGrid := by simp [room', getRoomObs]
    have h1 : s.grid = buildCenterGrid bs := hgrid
    rw [h0, h1] at h_eq
    have : buildEastGrid ≠ buildCenterGrid bs := by
      simp[buildCenterGrid,buildEastGrid];exists 0;simp[ROOM_H,ROOM_W];exists 4;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem east_west_to_center (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildEastGrid) (hplayer : s.player = some (0, 4))
    (hexits : s.exits = [EAST_EXIT_WEST]) (hbs : bs = BridgeState.westToEast):
    Step s b Action.left (getRoomObs 1 CENTER_SPAWN_FROM_EAST bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 1 CENTER_SPAWN_FROM_EAST bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.left := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.left s.exits := by
    simp [hplayer, hexits, EAST_EXIT_WEST, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildCenterGrid bs := by simp [room', getRoomObs]
    have h1 : s.grid = buildEastGrid := hgrid
    rw [h0, h1] at h_eq
    have : buildCenterGrid bs ≠ buildEastGrid := by
      simp[buildCenterGrid,buildEastGrid];exists 0;simp[ROOM_H,ROOM_W];exists 4;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; unfold buildCenterGrid; simp [bridgeTiles]
    simp [isSafeMoveB,CENTER_SPAWN_FROM_EAST,inBoundsB,isBlockedB,ROOM_W,ROOM_H,getTile,CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH,TILE_WALL,TILE_BRIDGE,TILE_BRIDGE,TILE_GAP,TILE_TRAP,TILE_CHEST,TILE_EXIT,TILE_MONSTER]
    rw[hbs];simp
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem center_south_to_south (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildCenterGrid bs) (hplayer : s.player = some (4, 7))
    (hexits : s.exits = [CENTER_EXIT_WEST, CENTER_EXIT_EAST, CENTER_EXIT_NORTH, CENTER_EXIT_SOUTH]) :
    Step s b Action.down (getRoomObs 4 SOUTH_SPAWN bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 4 SOUTH_SPAWN bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.down := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.down s.exits := by
    simp [hplayer, hexits, CENTER_EXIT_SOUTH, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildSouthGrid := by simp [room', getRoomObs]
    have h1 : s.grid = buildCenterGrid bs := hgrid
    rw [h0, h1] at h_eq
    have : buildSouthGrid ≠ buildCenterGrid bs := by
      simp[buildCenterGrid,buildSouthGrid];exists 4;simp[ROOM_H,ROOM_W];exists 0;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; native_decide
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

theorem south_north_to_center (s : SymbolicObs) (b : BeliefState) (bs : BridgeState)
    (hgrid : s.grid = buildSouthGrid) (hplayer : s.player = some (4, 0))
    (hexits : s.exits = [SOUTH_EXIT_NORTH]) (hbs : bs = BridgeState.westToSouth):
    Step s b Action.up (getRoomObs 1 CENTER_SPAWN_FROM_SOUTH bs).toSymbolicObs
      { b with step := b.step + 1 } :=
by
  let room' := (getRoomObs 1 CENTER_SPAWN_FROM_SOUTH bs).toSymbolicObs
  have hpos : s.player.isSome := by rw [hplayer]; simp
  have hmove : isMoveAction Action.up := by simp [isMoveAction]
  have hescape : isExitLeavingAction (s.player.get hpos) Action.up s.exits := by
    simp [hplayer, hexits, SOUTH_EXIT_NORTH, isExitLeavingAction, ROOM_W, ROOM_H]
  have hgrid_diff : room'.grid ≠ s.grid := by
    intro h_eq
    have h0 : room'.grid = buildCenterGrid bs := by simp [room', getRoomObs]
    have h1 : s.grid = buildSouthGrid := hgrid
    rw [h0, h1] at h_eq
    have : buildCenterGrid bs ≠ buildSouthGrid := by
      simp[buildCenterGrid,buildSouthGrid];exists 4;simp[ROOM_H,ROOM_W];exists 0;simp[CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH];native_decide
    exact this h_eq
  have hplayer_some : room'.player.isSome := by simp [room', getRoomObs]
  have hsafe_dest : isSafeMoveB room'.grid (room'.player.get hplayer_some) = true := by
    simp [room', getRoomObs]; unfold buildCenterGrid; simp [bridgeTiles]
    simp [isSafeMoveB,CENTER_SPAWN_FROM_SOUTH,inBoundsB,isBlockedB,ROOM_W,ROOM_H,getTile,CENTER_EXIT_WEST,CENTER_EXIT_EAST,CENTER_EXIT_NORTH,CENTER_EXIT_SOUTH,TILE_WALL,TILE_BRIDGE,TILE_BRIDGE,TILE_GAP,TILE_TRAP,TILE_CHEST,TILE_EXIT,TILE_MONSTER]
    rw[hbs];simp
  exact Step.roomTransition hpos hmove hescape hplayer_some hgrid_diff hsafe_dest

/- ================================================================
   10. 各房间路径安全
   ================================================================ -/

/-- west: spawn(7,4)→switch(4,4)→exit(9,4) -/
def west_path : List Position := [
  (6,4),(5,4),(4,4),         -- spawn→switch
  (5,4),(6,4),(7,4),(8,4),(9,4)  -- switch→exit
]

theorem west_path_safe : ∀ p ∈ west_path, isSafeMove buildWestGrid p := by
  simp [west_path, isSafeMove, isBlocked, inBounds, getTile,
    buildWestGrid, WEST_WALLS, WEST_SWITCH, WEST_EXIT_EAST, ROOM_W, ROOM_H,
    TILE_EMPTY, TILE_WALL, TILE_EXIT, TILE_SWITCH]
  all_goals { native_decide }

/-- center: 从各个入口出发到出口，沿桥走 -/
def center_path_westToNorth (bs : BridgeState) : List Position :=
  match bs with
  | BridgeState.westToNorth => [(1,4),(2,4),(3,4),(4,4),(4,3),(4,2),(4,1),(4,0)]
  | _ => []

def center_path_northToWest (bs : BridgeState) : List Position :=
  match bs with
  | BridgeState.westToNorth => [(4,1),(4,2),(4,3),(4,4),(3,4),(2,4),(1,4),(0,4)]
  | _ => []

/-- north: spawn(4,1)→chest(4,3)→exit(4,7) -/
def north_path : List Position := [
  (4,2),(3,2),(3,3),(3,4),(4,4),(4,5),(4,6),(4,7)
]

theorem north_path_safe : ∀ p ∈ north_path, isSafeMove buildNorthGrid p := by
  simp [north_path, isSafeMove, isBlocked, inBounds, getTile,
    buildNorthGrid, NORTH_WALLS, NORTH_CHEST, NORTH_EXIT_SOUTH, ROOM_W, ROOM_H,
    TILE_EMPTY, TILE_WALL, TILE_CHEST, TILE_EXIT]
  all_goals { native_decide }

/-- east: spawn(1,4)→chest(5,4)→exit(0,4) -/
def east_path : List Position := [
  (2,4),(3,4),(4,4),     -- spawn→chest
  (3,4),(2,4),(1,4),(0,4)  -- chest→exit
]

theorem east_path_safe : ∀ p ∈ east_path, isSafeMove buildEastGrid p := by
  simp [east_path, isSafeMove, isBlocked, inBounds, getTile,
    buildEastGrid, EAST_WALLS, EAST_CHEST, EAST_EXIT_WEST, ROOM_W, ROOM_H,
    TILE_EMPTY, TILE_WALL, TILE_CHEST, TILE_EXIT,WEST_WALLS]
  all_goals { native_decide }

/-- south: spawn(4,6)→monster(4,4)→exit(4,0) -/
def south_path : List Position := [
  (4,5),(4,4),         -- spawn→monster
  (4,3),(4,2),(4,1),(4,0)  -- monster→exit
]

theorem south_path_safe : ∀ p ∈ south_path, isSafeMove buildSouthGrid p := by
  simp [south_path, isSafeMove, isBlocked, inBounds, getTile,
    buildSouthGrid, SOUTH_WALLS, SOUTH_EXIT_NORTH, ROOM_W, ROOM_H,
    TILE_EMPTY, TILE_WALL, TILE_EXIT]
  all_goals { native_decide }

/- ================================================================
   11. 单步移动引理
   ================================================================ -/

theorem step_west_left (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildWestGrid) (hp : s.player = some (x, y))
    (hsafe : (x-1, y) ∈ west_path) :
    Step s b Action.left { s with player := some (x-1, y), facing := Direction.left }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.left) := by
    simpa [hg, hp, nextPosition] using west_path_safe (x-1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_west_right (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildWestGrid) (hp : s.player = some (x, y))
    (hsafe : (x+1, y) ∈ west_path) :
    Step s b Action.right { s with player := some (x+1, y), facing := Direction.right }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.right) := by
    simpa [hg, hp, nextPosition] using west_path_safe (x+1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_north_down (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildNorthGrid) (hp : s.player = some (x, y))
    (hsafe : (x, y+1) ∈ north_path) :
    Step s b Action.down { s with player := some (x, y+1), facing := Direction.down }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.down) := by
    simpa [hg, hp, nextPosition] using north_path_safe (x, y+1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_north_up (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildNorthGrid) (hp : s.player = some (x, y))
    (hsafe : (x, y-1) ∈ north_path) :
    Step s b Action.up { s with player := some (x, y-1), facing := Direction.up }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.up) := by
    simpa [hg, hp, nextPosition] using north_path_safe (x, y-1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_east_left (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildEastGrid) (hp : s.player = some (x, y))
    (hsafe : (x-1, y) ∈ east_path) :
    Step s b Action.left { s with player := some (x-1, y), facing := Direction.left }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.left) := by
    simpa [hg, hp, nextPosition] using east_path_safe (x-1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_east_right (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildEastGrid) (hp : s.player = some (x, y))
    (hsafe : (x+1, y) ∈ east_path) :
    Step s b Action.right { s with player := some (x+1, y), facing := Direction.right }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.right) := by
    simpa [hg, hp, nextPosition] using east_path_safe (x+1, y) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_south_down (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildSouthGrid) (hp : s.player = some (x, y))
    (hsafe : (x, y+1) ∈ south_path) :
    Step s b Action.down { s with player := some (x, y+1), facing := Direction.down }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.down) := by
    simpa [hg, hp, nextPosition] using south_path_safe (x, y+1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

theorem step_south_up (s : SymbolicObs) (b : BeliefState) (x y : Nat)
    (hg : s.grid = buildSouthGrid) (hp : s.player = some (x, y))
    (hsafe : (x, y-1) ∈ south_path) :
    Step s b Action.up { s with player := some (x, y-1), facing := Direction.up }
      { b with step := b.step + 1 } := by
  have hpos : s.player.isSome := by rw [hp]; simp
  have h_safe : isSafeMove s.grid (nextPosition (s.player.get hpos) Action.up) := by
    simpa [hg, hp, nextPosition] using south_path_safe (x, y-1) hsafe
  simpa [hp, nextPosition] using Step.moveSafe hpos (by simp [isMoveAction]) h_safe

/- ================================================================
   12. 任务完成条件
   ================================================================ -/

def task4Goal : TaskGoal :=
  {
    monstersDefeated := true
    keyCollected     := true
    chestOpened      := true
    exitReached      := false
    allChestsOpened  := false
  }

/- ================================================================
   13. Exec 框架 — 各阶段子目标
   ================================================================ -/

/-- Phase 1: west spawn(7,4)→switch(4,4) 按开关切换桥→north方向 [3步+buttonA] -/
def plan_phase1 : List Action :=
  [Action.left, Action.left, Action.left, Action.buttonA]

/-- Phase 2: west(4,4)→exit(9,4)→center→north→拿钥匙 [需要桥状态 westToNorth] -/
def plan_phase2 : List Action :=
  [Action.right, Action.right, Action.right, Action.right, Action.right] ++  -- west→exit
  [Action.right] ++  -- 房间切换→center
  [Action.up, Action.up, Action.up, Action.up] ++  -- center→north exit
  [Action.up] ++  -- 房间切换→north
  [Action.down, Action.buttonA]  -- north spawn→chest→开箱

/-- Phase 3: north→exit→center→west→按开关切换桥→east方向 -/
def plan_phase3 : List Action :=
  [Action.down, Action.down, Action.down, Action.down, Action.down] ++  -- north→exit
  [Action.down] ++  -- 房间切换→center
  [Action.left, Action.left, Action.left, Action.left] ++  -- center→west exit
  [Action.left] ++  -- 房间切换→west
  [Action.left, Action.left, Action.left, Action.buttonA]  -- west→switch→按钮

/-- Phase 4: west→exit→center→east→拿剑 [需要桥状态 westToEast] -/
def plan_phase4 : List Action :=
  [Action.right, Action.right, Action.right, Action.right, Action.right] ++  -- west→exit
  [Action.right] ++  -- 房间切换→center
  [Action.right, Action.right, Action.right, Action.right, Action.right, Action.right, Action.right, Action.right] ++  -- center→east exit
  [Action.right] ++  -- 房间切换→east（锁门，需钥匙）
  [Action.left, Action.left, Action.left, Action.left, Action.buttonA]  -- east spawn→chest→开箱拿剑

/-- Phase 5: east→center→west→按开关→south方向 -/
def plan_phase5 : List Action :=
  [Action.right, Action.right, Action.right, Action.right, Action.right] ++  -- east→exit
  [Action.left] ++  -- 房间切换→center
  [Action.left, Action.left, Action.left, Action.left, Action.left, Action.left, Action.left, Action.left] ++  -- center→west exit
  [Action.left] ++  -- 房间切换→west
  [Action.left, Action.left, Action.left, Action.buttonA]  -- west→switch→按钮

/-- Phase 6: west→center→south→杀怪 [需要桥状态 westToSouth] -/
def plan_phase6 : List Action :=
  [Action.right, Action.right, Action.right, Action.right, Action.right] ++  -- west→exit
  [Action.right] ++  -- 房间切换→center
  [Action.down, Action.down, Action.down, Action.down, Action.down, Action.down, Action.down] ++  -- center→south exit
  [Action.down] ++  -- 房间切换→south
  [Action.up, Action.up] ++  -- south spawn→monster
  [Action.buttonA]  -- 杀怪

/-- Phase 7: south→center→开最终宝箱 -/
def plan_phase7 : List Action :=
  [Action.up, Action.up, Action.up, Action.up] ++  -- south→exit
  [Action.up] ++  -- 房间切换→center
  [Action.wait] ++  -- 最终宝箱显现
  [Action.left, Action.left, Action.left, Action.left, Action.buttonA]  -- 开最终宝箱

/-- 总计划 -/
def full_plan : List Action :=
  plan_phase1 ++ plan_phase2 ++ plan_phase3 ++ plan_phase4 ++
  plan_phase5 ++ plan_phase6 ++ plan_phase7

theorem task4_plan_steps_lt_max : full_plan.length < TASK4_MAX_STEPS := by
  native_decide

/- ================================================================
   14. 主定理
   ================================================================

   由于 Task 4 涉及动态桥状态、开关切换和扩展 Step 规则，
   完整的 Exec 证明需要自定义 Step4 归纳类型的支持，
   以及额外的房间切换定理将 Step 提升到 Step4。
   以下仅给出计划规格，不将其表述为完整可完成性证明。

   完整的 Exec 链构造（将每一步显式展开为 Step4.inheritStep 或
   Step4.activateSwitch 等）留待后续补充具体路径细节。
   ================================================================ -/

/-- Task 4 的候选计划规格。
    该定义刻画已枚举的阶段计划、预算和目标对象，但**不**声称已经
    构造完整的动态 `Exec` 链；完整可完成性必须在补齐 Step4 后另行证明。 -/
def Task4PlanSpecification : Prop :=
  full_plan.length < TASK4_MAX_STEPS ∧
  NORTH_CHEST ∈ [NORTH_CHEST, EAST_CHEST, CENTER_FINAL_CHEST] ∧
  EAST_CHEST ∈ [NORTH_CHEST, EAST_CHEST, CENTER_FINAL_CHEST] ∧
  CENTER_FINAL_CHEST ∈ [NORTH_CHEST, EAST_CHEST, CENTER_FINAL_CHEST] ∧
  SOUTH_MONSTER = SOUTH_MONSTER

theorem task4_plan_specification : Task4PlanSpecification := by
  unfold Task4PlanSpecification
  constructor
  · exact task4_plan_steps_lt_max
  · native_decide

/- ================================================================
   15. 综合总结定理
   ================================================================ -/

theorem task4_formalization_summary :
    Task4PlanSpecification ∧
    full_plan.length < TASK4_MAX_STEPS ∧
    roomReachable task4RoomGraph ROOM_WEST ROOM_NORTH ∧
    roomReachable task4RoomGraph ROOM_WEST ROOM_EAST ∧
    roomReachable task4RoomGraph ROOM_WEST ROOM_SOUTH := by
  refine ⟨task4_plan_specification, task4_plan_steps_lt_max, ?_, ?_, ?_⟩
  · exact all_rooms_reachable.1
  · exact all_rooms_reachable.2.1
  · exact all_rooms_reachable.2.2

end Task4
