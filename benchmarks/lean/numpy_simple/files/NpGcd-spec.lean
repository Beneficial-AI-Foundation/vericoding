-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcdInt (a b : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcdInt_spec (a b : Int) :
  gcdInt a b ≥ 0 ∧
  a % gcdInt a b = 0 ∧
  b % gcdInt a b = 0 ∧
  ∀ d : Int, d > 0 → a % d = 0 → b % d = 0 → d ≤ gcdInt a b :=
sorry
-- </vc-theorems>