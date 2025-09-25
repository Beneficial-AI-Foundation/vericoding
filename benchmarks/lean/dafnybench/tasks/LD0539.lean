-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Reverse (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_spec (a : Array Int) (aRev : Array Int) :
aRev = Reverse a →
(aRev.size = a.size) ∧
(∀ i, 0 ≤ i ∧ i < a.size → a[i]! = aRev[(aRev.size - i - 1)]!) :=
sorry
-- </vc-theorems>