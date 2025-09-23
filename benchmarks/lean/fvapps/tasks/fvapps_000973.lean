-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_chakra_needed (n m : Nat) (soint_powers soint_levels sofloat_powers sofloat_levels : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_chakra_cases :
  (min_chakra_needed 1 1 [10] [1] [5] [1] = 0) ∧
  (min_chakra_needed 2 2 [10, 20] [1, 2] [5, 15] [1, 2] = 0) ∧
  (min_chakra_needed 2 3 [10, 20] [1, 2] [5, 5, 18] [2, 2, 1] = 8) ∧
  (min_chakra_needed 2 2 [10, 10] [1, 1] [20, 20] [1, 1] = 20) :=
sorry
-- </vc-theorems>