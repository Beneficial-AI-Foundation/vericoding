-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat :=
  sorry

def check_divisible_permutations (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_divisible_permutations_valid_output (n : Nat) :
  n > 0 → check_divisible_permutations n = 0 ∨ check_divisible_permutations n = 1 :=
sorry

theorem check_divisible_permutations_single_digits :
  check_divisible_permutations 1 = 0 ∧ check_divisible_permutations 2 = 1 :=
sorry
-- </vc-theorems>