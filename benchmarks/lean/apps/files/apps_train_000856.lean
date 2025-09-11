-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nondecreasing_subarrays (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem always_returns_positive {arr : List Int} (h : arr ≠ []) : 
  count_nondecreasing_subarrays arr > 0 :=
sorry

theorem single_element_returns_one {arr : List Int} (h : arr.length = 1) :
  count_nondecreasing_subarrays arr = 1 :=
sorry

theorem count_at_least_length {arr : List Int} (h : arr.length ≥ 2) :
  count_nondecreasing_subarrays arr ≥ arr.length :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_nondecreasing_subarrays [1, 4, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_nondecreasing_subarrays [5]

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_nondecreasing_subarrays [1, 2, 3, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible