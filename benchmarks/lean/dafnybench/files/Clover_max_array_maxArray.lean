-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxArray (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxArray_spec (a : Array Int) :
a.size ≥ 1 →
let m := maxArray a
(∀ k, 0 ≤ k ∧ k < a.size → m ≥ a[k]!) ∧
(∃ k, 0 ≤ k ∧ k < a.size ∧ m = a[k]!) :=
sorry
-- </vc-theorems>