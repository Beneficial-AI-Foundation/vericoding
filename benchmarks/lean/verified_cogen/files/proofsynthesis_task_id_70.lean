-- <vc-preamble>
@[reducible, simp]
def allSequenceEqualLength_precond (seq : Array (Array Int)) :=
  seq.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allSequenceEqualLength (seq : Array (Array Int)) (h_precond : allSequenceEqualLength_precond seq) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def allSequenceEqualLength_postcond (seq : Array (Array Int)) (result: Bool) (h_precond : allSequenceEqualLength_precond seq) :=
  (∀ i j, i < seq.size → j < seq.size → seq[i]!.size = seq[j]!.size) ↔ result

theorem allSequenceEqualLength_spec_satisfied (seq: Array (Array Int)) (h_precond : allSequenceEqualLength_precond seq) :
    allSequenceEqualLength_postcond seq (allSequenceEqualLength seq h_precond) h_precond := by
  sorry
-- </vc-theorems>