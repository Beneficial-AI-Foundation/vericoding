-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsEvenAtIndexEven (lst : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsEvenAtIndexEven_spec (lst : Array Int) :
IsEvenAtIndexEven lst = (∀ i, 0 ≤ i ∧ i < lst.size → (IsEven i → IsEven (lst[i]!))) :=
sorry
-- </vc-theorems>