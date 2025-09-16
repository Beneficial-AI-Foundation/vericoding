-- <vc-preamble>
def min_subarray_len (target : Nat) (nums : List Nat) : Nat :=
sorry

def sum_list (l : List Nat) : Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def slice (l : List Nat) (start : Nat) (len : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_subarray_len_empty {target : Nat} :
  min_subarray_len target [] = 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_subarray_len 7 [2, 3, 1, 2, 4, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_subarray_len 5 []

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_subarray_len 10 [1, 1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible