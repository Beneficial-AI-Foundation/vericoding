-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AnyValueExists (seq1 : Array Int) (seq2 : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AnyValueExists_spec (seq1 seq2 : Array Int) :
AnyValueExists seq1 seq2 ↔ (∃ i, 0 ≤ i ∧ i < seq1.size ∧ seq2.contains (seq1[i]!)) :=
sorry
-- </vc-theorems>