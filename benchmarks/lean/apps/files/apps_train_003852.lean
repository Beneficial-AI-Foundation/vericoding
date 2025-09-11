-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem last_element_always_included {arr : List Int} (h : arr ≠ []) :
  (solve arr).getLast? = arr.getLast? :=
  sorry

theorem result_subset_of_input {arr : List Int} (h : arr ≠ []) :
  ∀ x : Int, x ∈ solve arr → x ∈ arr :=
  sorry

/-
info: [21, 7, 5]
-/
-- #guard_msgs in
-- #eval solve [1, 21, 4, 7, 5]

/-
info: [5, 4, 3, 2, 1]
-/
-- #guard_msgs in
-- #eval solve [5, 4, 3, 2, 1]

/-
info: [17, 14, 5, 2]
-/
-- #guard_msgs in
-- #eval solve [16, 17, 14, 3, 14, 5, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible