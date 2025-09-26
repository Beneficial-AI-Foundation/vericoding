-- <vc-preamble>
def knights_tour (start : Pos) (size : Nat) : List Pos :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_knight_move (p1 p2 : Pos) : Bool :=
  let dx := if p1.x ≥ p2.x then p1.x - p2.x else p2.x - p1.x
  let dy := if p1.y ≥ p2.y then p1.y - p2.y else p2.y - p1.y
  (dx == 2 && dy == 1) || (dx == 1 && dy == 2)
-- </vc-definitions>

-- <vc-theorems>
theorem knights_tour_returns_valid_path (start : Pos) (size : Nat) 
    (h1 : size ≥ 5) (h2 : start.x < size) (h2' : start.y < size) :
    let path := knights_tour start size
    -- Path has correct length
    (path.length = size * size) ∧ 
    -- Starts at given position
    (path.head? = some start) ∧
    -- All positions are within bounds
    (∀ p ∈ path, p.x < size ∧ p.y < size) ∧
    -- All positions are unique
    (∀ i j, i < path.length → j < path.length → i ≠ j → path.get! i ≠ path.get! j) ∧
    -- All moves are valid knight moves
    (∀ i, i < path.length - 1 → is_valid_knight_move (path.get! i) (path.get! (i+1))) := by
  sorry

theorem small_boards_sequential (size : Nat) (h : size ≤ 4) :
    let start := ⟨0,0⟩
    let path := knights_tour start size
    let expected := (List.range size).bind (fun x => 
      (List.range size).map (fun y => ⟨x,y⟩))
    path = expected := by
  sorry

/-
info: 25
-/
-- #guard_msgs in
-- #eval len knights_tour((0, 0), 5)

/-
info: 36
-/
-- #guard_msgs in
-- #eval len knights_tour((2, 2), 6)

/-
info: 64
-/
-- #guard_msgs in
-- #eval len knights_tour((0, 0), 8)
-- </vc-theorems>