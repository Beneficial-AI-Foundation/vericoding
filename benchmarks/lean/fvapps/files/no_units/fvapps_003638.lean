-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def all_permuted (n : Nat) : Nat := sorry

theorem all_permuted_nonnegative (n : Nat) : 
  all_permuted n ≥ 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_permuted_base_cases : 
  all_permuted 1 = 0 ∧ all_permuted 2 = 1 :=
sorry

theorem all_permuted_increases (n : Nat) :
  n > 2 → all_permuted n > all_permuted (n-1) :=
sorry
-- </vc-theorems>