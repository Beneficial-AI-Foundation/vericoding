-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsNonPrime (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsNonPrime_spec (n : Int) :
n ≥ 2 →
IsNonPrime n = true ↔ (∃ k : Int, 2 ≤ k ∧ k < n ∧ n % k = 0) :=
sorry
-- </vc-theorems>