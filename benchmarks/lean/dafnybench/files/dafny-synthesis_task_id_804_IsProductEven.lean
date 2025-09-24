-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsProductEven (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsProductEven_spec (a : Array Int) :
IsProductEven a ↔ ∃ i, 0 ≤ i ∧ i < a.size ∧ IsEven (a[i]!) :=
sorry
-- </vc-theorems>