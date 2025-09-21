-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Reverse (a : Array Char) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_spec (a : Array Char) (b : Array Char) :
a.size > 0 →
b = Reverse a →
(b.size = a.size ∧
∀ i, 0 ≤ i ∧ i < a.size → b[i]! = a[a.size - i - 1]!) :=
sorry
-- </vc-theorems>