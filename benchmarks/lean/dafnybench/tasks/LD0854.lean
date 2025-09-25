-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PalVerify (a : Array Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem PalVerify_spec (a : Array Char) :
let yn := PalVerify a
(yn = true → ∀ i, 0 ≤ i ∧ i < a.size/2 → a[i]! = a[a.size - i - 1]!) ∧
(yn = false → ∃ i, 0 ≤ i ∧ i < a.size/2 ∧ a[i]! ≠ a[a.size - i - 1]!) ∧
(∀ j, 0 ≤ j ∧ j < a.size → a[j]! = a[j]!) :=
sorry
-- </vc-theorems>