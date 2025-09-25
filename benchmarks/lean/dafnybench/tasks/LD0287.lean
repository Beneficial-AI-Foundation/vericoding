-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Reverse (a : Array Char) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_spec (a : Array Char) :
a.size > 0 →
let b := Reverse a
(b.size = a.size) ∧
(∀ k, 0 ≤ k ∧ k < a.size → b[k]! = a[((a.size - 1) - k)]!) :=
sorry
-- </vc-theorems>