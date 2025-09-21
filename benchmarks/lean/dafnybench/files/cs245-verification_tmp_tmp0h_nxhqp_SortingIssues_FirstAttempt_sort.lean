-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort (A : Array Int) (n : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_spec (A : Array Int) (n : Int) :
n = A.size ∧
n ≥ 0 →
∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < n →
(sort A n)[i.toNat]! ≤ (sort A n)[j.toNat]! :=
sorry
-- </vc-theorems>