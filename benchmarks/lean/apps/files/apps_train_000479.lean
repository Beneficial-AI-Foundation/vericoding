/-
There are N rooms and you start in room 0.  Each room has a distinct number in 0, 1, 2, ..., N-1, and each room may have some keys to access the next room. 
Formally, each room i has a list of keys rooms[i], and each key rooms[i][j] is an integer in [0, 1, ..., N-1] where N = rooms.length.  A key rooms[i][j] = v opens the room with number v.
Initially, all the rooms start locked (except for room 0). 
You can walk back and forth between rooms freely.
Return true if and only if you can enter every room.

Example 1:
Input: [[1],[2],[3],[]]
Output: true
Explanation:  
We start in room 0, and pick up key 1.
We then go to room 1, and pick up key 2.
We then go to room 2, and pick up key 3.
We then go to room 3.  Since we were able to go to every room, we return true.

Example 2:
Input: [[1,3],[3,0,1],[2],[0]]
Output: false
Explanation: We can't enter the room with number 2.

Note:

1 <= rooms.length <= 1000
0 <= rooms[i].length <= 1000
The number of keys in all rooms combined is at most 3000.
-/

-- <vc-helpers>
-- </vc-helpers>

def canVisitAllRooms (rooms : List (List Nat)) : Bool := sorry

theorem canVisitAllRooms_bool 
  (rooms : List (List Nat)) : 
  canVisitAllRooms rooms = true ∨ canVisitAllRooms rooms = false := sorry

theorem canVisitAllRooms_reachable
  (rooms : List (List Nat))
  (h : canVisitAllRooms rooms = true) :
  ∀ i < rooms.length, ∃ path : List Nat, 
    path.head? = some 0 ∧ 
    path.getLast? = some i ∧
    ∀ j < path.length - 1,
      (rooms[path[j]!]!).contains (path[j+1]!) := sorry

theorem canVisitAllRooms_unreachable
  (rooms : List (List Nat))
  (h : canVisitAllRooms rooms = false) :
  ∃ i < rooms.length,
    ∀ path : List Nat,
    ¬(path.head? = some 0 ∧ 
      path.getLast? = some i ∧
      ∀ j < path.length - 1,
        (rooms[path[j]!]!).contains (path[j+1]!)) := sorry

theorem canVisitAllRooms_preserves_input
  (rooms : List (List Nat))
  (rooms_copy := rooms) :
  canVisitAllRooms rooms = canVisitAllRooms rooms_copy := sorry

theorem canVisitAllRooms_single_room :
  canVisitAllRooms [[]] = true := sorry

theorem canVisitAllRooms_self_ref :
  canVisitAllRooms [[0]] = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_visit_all_rooms [[1], [2], [3], []]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_visit_all_rooms [[1, 3], [3, 0, 1], [2], [0]]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_visit_all_rooms [[1], [2], [3], [], [], []]

-- Apps difficulty: interview
-- Assurance level: unguarded