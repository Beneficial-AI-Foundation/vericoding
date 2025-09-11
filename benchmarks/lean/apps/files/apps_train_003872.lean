-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def performant_smallest (arr : List Int) (n : Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem performant_smallest_length_eq_n {arr : List Int} {n : Nat} 
  (h : 0 < arr.length) (h2 : n ≤ arr.length) :
  (performant_smallest arr n).length = n :=
sorry

theorem performant_smallest_elements_from_arr {arr : List Int} {n : Nat} 
  (h : 0 < arr.length) (h2 : n ≤ arr.length) :
  ∀ x, x ∈ performant_smallest arr n → x ∈ arr :=
sorry

theorem performant_smallest_full_list {arr : List Int} (h : 0 < arr.length) :
  performant_smallest arr arr.length = arr :=
sorry

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval performant_smallest [1, 2, 3, 4, 5] 3

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval performant_smallest [5, 4, 3, 2, 1] 3

/-
info: [2, 1, 2]
-/
-- #guard_msgs in
-- #eval performant_smallest [2, 1, 3, 2, 3] 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible