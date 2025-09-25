-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallest_range_i (arr : List Int) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem smallest_range_i_non_negative {arr : List Int} {k : Nat} (h : arr.length > 0) :
  smallest_range_i arr k ≥ 0 := sorry

theorem smallest_range_i_single_element {arr : List Int} {k : Nat} (h : arr.length = 1) : 
  smallest_range_i arr k = 0 := sorry

theorem smallest_range_i_bound {arr : List Int} {k : Nat} (h : arr.length > 0) :
  smallest_range_i arr k ≤ (arr.maximum?.getD 0) - (arr.minimum?.getD 0) := sorry

theorem smallest_range_i_reduction {arr : List Int} {k : Nat} (h : arr.length > 0) :
  smallest_range_i arr k = max 0 ((arr.maximum?.getD 0) - (arr.minimum?.getD 0) - 2 * k) := sorry

theorem smallest_range_i_zero_k {arr : List Int} (h₁ : arr.length > 0) (h₂ : arr.length > 1) :
  smallest_range_i arr 0 = (arr.maximum?.getD 0) - (arr.minimum?.getD 0) := sorry

theorem smallest_range_i_large_k {arr : List Int} {k : Nat} (h₁ : arr.length > 0)
  (h₂ : k ≥ (arr.maximum?.getD 0) - (arr.minimum?.getD 0)) :
  smallest_range_i arr k = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallest_range_i [1] 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval smallest_range_i [0, 10] 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallest_range_i [1, 3, 6] 3
-- </vc-theorems>