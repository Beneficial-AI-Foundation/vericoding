-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ContainsSequence (list : Array (Array Int)) (sub : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ContainsSequence_spec (list : Array (Array Int)) (sub : Array Int) :
ContainsSequence list sub = (∃ i, 0 ≤ i ∧ i < list.size ∧ sub = list[i]!) :=
sorry
-- </vc-theorems>