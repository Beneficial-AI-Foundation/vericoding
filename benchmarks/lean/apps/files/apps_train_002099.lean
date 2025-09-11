-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_permutation (n : Nat) (arr : List Nat) : Nat := sorry 

theorem permutation_result_nonnegative (n : Nat) (arr : List Nat) :
  solve_permutation n arr ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_result_bounded (n : Nat) (arr : List Nat) :
  solve_permutation n arr ≤ arr.length := sorry

theorem single_element_zero (x : Nat) :
  solve_permutation 1 [x] = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_permutation 7 [10, 1, 1, 1, 5, 5, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_permutation 5 [1, 1, 1, 1, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_permutation 6 [300000000, 200000000, 300000000, 200000000, 1000000000, 300000000]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible