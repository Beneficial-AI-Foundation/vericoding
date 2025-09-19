-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>