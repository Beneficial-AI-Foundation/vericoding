-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsPrime (m : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsPrime_spec (m : Int) :
m > 0 →
(IsPrime m ↔ (m > 1 ∧ ∀ j : Int, 2 ≤ j ∧ j < m → m % j ≠ 0)) :=
sorry
-- </vc-theorems>