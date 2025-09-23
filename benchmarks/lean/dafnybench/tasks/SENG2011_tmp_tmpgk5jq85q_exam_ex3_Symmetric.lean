-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Symmetric (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Symmetric_spec (a : Array Int) :
let flag := Symmetric a
(flag = true → ∀ x, 0 ≤ x ∧ x < a.size → a[x]! = a[a.size - x - 1]!) ∧
(flag = false → ∃ x, 0 ≤ x ∧ x < a.size ∧ a[x]! ≠ a[a.size - x - 1]!) :=
sorry
-- </vc-theorems>