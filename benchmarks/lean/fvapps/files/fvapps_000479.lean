-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def canVisitAllRooms (rooms : List (List Nat)) : Bool := sorry

theorem canVisitAllRooms_bool 
  (rooms : List (List Nat)) : 
  canVisitAllRooms rooms = true ∨ canVisitAllRooms rooms = false := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>