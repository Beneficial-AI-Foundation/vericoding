-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_if_exist (arr : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_if_exist_symmetric {arr : List Int} (n : Int) :
  arr ≠ [] →
  check_if_exist (arr ++ [2 * n]) = true :=
sorry

theorem check_if_exist_no_doubles (arr : List Int) :
  (∀ x ∈ arr, ∀ y ∈ arr, x ≠ 2 * y ∧ 2 * x ≠ y) →
  check_if_exist arr = false :=
sorry

theorem check_if_exist_zero (arr : List Int) :
  arr ≠ [] →
  check_if_exist (arr ++ [0, 0]) = true :=
sorry

theorem check_if_exist_empty :
  check_if_exist ([] : List Int) = false :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_if_exist [10, 2, 5, 3]

/-
info: True
-/
-- #guard_msgs in
-- #eval check_if_exist [7, 1, 14, 11]

/-
info: False
-/
-- #guard_msgs in
-- #eval check_if_exist [3, 1, 7, 11]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded