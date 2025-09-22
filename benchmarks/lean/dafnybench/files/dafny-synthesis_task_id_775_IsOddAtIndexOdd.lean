-- <vc-preamble>
def IsOdd (n : Int) : Bool :=
n % 2 = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsOddAtIndexOdd (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsOddAtIndexOdd_spec (a : Array Int) :
IsOddAtIndexOdd a = (∀ i, 0 ≤ i ∧ i < a.size → (IsOdd i → IsOdd (a[i]!))) :=
sorry
-- </vc-theorems>