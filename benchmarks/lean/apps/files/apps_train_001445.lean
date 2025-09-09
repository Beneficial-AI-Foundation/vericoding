-- <vc-helpers>
-- </vc-helpers>

def min_moves_to_catch (h x y : Nat) : Int := sorry

theorem result_valid (n : Nat) :
  let result := min_moves_to_catch (n + 1) n n
  result = -1 ∨ result > 0 := sorry

theorem equal_positions_catchable (n : Nat) : 
  let h := n * n + 1
  min_moves_to_catch h n n ≠ -1 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_moves_to_catch 101 10 10

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_moves_to_catch 11 3 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_moves_to_catch 21 5 5

-- Apps difficulty: interview
-- Assurance level: unguarded