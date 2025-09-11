-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_exam (arr1 arr2 : List Char) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_exam_non_negative (arr1 arr2 : List Char) : 
  check_exam arr1 arr2 ≥ 0 :=
  sorry

theorem check_exam_perfect_score {arr1 arr2 : List Char} (h : arr1 = arr2) :  
  check_exam arr1 arr2 = 4 * arr1.length :=
  sorry 

theorem check_exam_empty_answers {arr1 arr2 : List Char} 
  (h : ∀ x, x ∈ arr2 → x = ' ') :
  check_exam arr1 arr2 = 0 :=
  sorry

theorem check_exam_imperfect_score {arr1 arr2 : List Char} 
  (h : arr1.length = arr2.length) (h2 : arr1 ≠ arr2) :
  check_exam arr1 arr2 < 4 * arr1.length :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval check_exam ["a", "a", "b", "b"] ["a", "c", "b", "d"]

/-
info: 7
-/
-- #guard_msgs in
-- #eval check_exam ["a", "a", "c", "b"] ["a", "a", "b", ""]

/-
info: 0
-/
-- #guard_msgs in
-- #eval check_exam ["b", "c", "b", "a"] ["", "a", "a", "c"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded