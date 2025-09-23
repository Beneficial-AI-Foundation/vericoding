-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_after_operations (n: Nat) (ops: List Operation) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_ops_is_zero (n: Nat) : 
  find_max_after_operations n [] = 0 :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_max_after_operations 2 ["RowAdd 1 3", "ColAdd 2 1", "ColAdd 1 4", "RowAdd 2 1"]

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_max_after_operations 3 ["RowAdd 1 5", "ColAdd 3 2", "RowAdd 2 4"]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_max_after_operations 1 ["RowAdd 1 3", "ColAdd 1 2"]
-- </vc-theorems>