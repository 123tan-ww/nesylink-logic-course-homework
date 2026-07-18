# 形式化框架模式（从 Task5 总结）

所有 Task 形式化文件遵循统一模式：
1. 地图常量（walls/chests/monsters/exits/spawns）
2. `buildRoomNGrid` 网格构造器
3. `getRoomObs` 房间状态构造器
4. `exitToDest` 出口→目标映射
5. `RoomGraph` + 房间可达性定理（`RoomPath.step` 构造）
6. 房间切换定理（`Step.roomTransition`）
7. 路径安全定义（`roomN_path` + `roomN_path_safe`，用 `native_decide`）
8. 单步移动引理（`stepN_方向`）
9. 中间状态定义
10. Exec 链证明（phase 分段 + `exec_append` 拼接）
11. `taskN_completable : TaskCompletable ...` 主定理
12. `taskN_formalization_summary` 综合总结定理
