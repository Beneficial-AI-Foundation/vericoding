-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsPrime (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsPrime_spec (n : Int) :
n ≥ 2 →
(IsPrime n = true ↔ (∀ k : Int, 2 ≤ k ∧ k < n → n % k ≠ 0)) :=
sorry
-- </vc-theorems>