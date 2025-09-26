-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AllElementsEqual (a : Array Int) (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AllElementsEqual_spec (a : Array Int) (n : Int) :
(AllElementsEqual a n = true → ∀ i, 0 ≤ i ∧ i < a.size → a[i]! = n) ∧
(AllElementsEqual a n = false → ∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! ≠ n) :=
sorry
-- </vc-theorems>