-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_permutation (n : Nat) (p : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem test_small_cases_1 :
  find_smallest_permutation 4 [3,2,4,1] = [3,1,2,4] :=
sorry

theorem test_small_cases_2 :
  find_smallest_permutation 2 [1,2] = [1,2] :=
sorry

theorem test_small_cases_3 :
  find_smallest_permutation 8 [4,6,3,2,8,5,7,1] = [3,1,2,7,4,6,8,5] :=
sorry

/-
info: [3, 1, 2, 4]
-/
-- #guard_msgs in
-- #eval find_smallest_permutation 4 [3, 2, 4, 1]

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval find_smallest_permutation 2 [1, 2]

/-
info: [3, 1, 2, 7, 4, 6, 8, 5]
-/
-- #guard_msgs in
-- #eval find_smallest_permutation 8 [4, 6, 3, 2, 8, 5, 7, 1]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded