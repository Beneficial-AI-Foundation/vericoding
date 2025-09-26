-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isZeroBalanced (arr : List Int) : Bool := sorry

theorem empty_array_not_balanced {arr : List Int} :
  arr = [] → ¬(isZeroBalanced arr) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem balanced_implies_sum_zero {arr : List Int} :
  isZeroBalanced arr → (arr.sum = 0) := sorry

theorem balanced_implies_equal_frequencies {arr : List Int} :
  isZeroBalanced arr → ∀ x, (List.countP (· = x) arr) = (List.countP (· = -x) arr) := sorry 

theorem all_zeros_array_balanced {arr : List Int} :
  arr ≠ [] → (∀ x ∈ arr, x = 0) → isZeroBalanced arr := sorry

theorem reverse_preserves_balance {arr : List Int} :
  isZeroBalanced arr → isZeroBalanced arr.reverse := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_zero_balanced []

/-
info: True
-/
-- #guard_msgs in
-- #eval is_zero_balanced [0, 1, -1]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_zero_balanced [3, -2, -1]
-- </vc-theorems>