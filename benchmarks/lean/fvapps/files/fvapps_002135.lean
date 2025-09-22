-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_kingdom (n : Nat) (roads : List (Nat × Nat)) (plans : List (Nat × List Nat)) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_kingdom_result_length {n : Nat} {roads : List (Nat × Nat)} {plans : List (Nat × List Nat)} :
  List.length (solve_kingdom n roads plans) = List.length plans :=
sorry

theorem solve_kingdom_result_valid_values {n : Nat} {roads : List (Nat × Nat)} {plans : List (Nat × List Nat)} :
  ∀ r ∈ solve_kingdom n roads plans, r = -1 ∨ r ≥ 0 :=
sorry 

theorem solve_kingdom_result_bounded {n : Nat} {roads : List (Nat × Nat)} {plans : List (Nat × List Nat)} :
  ∀ r ∈ solve_kingdom n roads plans, r = -1 ∨ r ≤ n :=
sorry
-- </vc-theorems>