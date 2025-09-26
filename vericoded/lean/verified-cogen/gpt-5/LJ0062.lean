import Mathlib
-- <vc-preamble>
@[reducible, simp]
def allSequenceEqualLength_precond (seq : Array (Array Int)) :=
  seq.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Classical

/-- Pairwise equality of in-bounds element lengths is equivalent to
    every element having the same length as the element at index 0. -/
lemma pairwise_eq_iff_all_eq_base
  (seq : Array (Array Int)) (h0 : 0 < seq.size) :
  (∀ i j, i < seq.size → j < seq.size → seq[i]!.size = seq[j]!.size)
    ↔ (∀ i : Fin seq.size, seq[i.val]!.size = seq[0]!.size) := by
  constructor
  · intro h i
    have hi : i.val < seq.size := i.isLt
    have hi0 : seq[i.val]!.size = seq[0]!.size := h i.val 0 hi h0
    simpa using hi0
  · intro h i j hi hj
    have hi' : seq[i]!.size = seq[0]!.size := h ⟨i, hi⟩
    have hj' : seq[j]!.size = seq[0]!.size := h ⟨j, hj⟩
    have hj'' : seq[0]!.size = seq[j]!.size := hj'.symm
    exact Eq.trans hi' hj''
-- </vc-helpers>

-- <vc-definitions>
def allSequenceEqualLength (seq : Array (Array Int)) (h_precond : allSequenceEqualLength_precond seq) : Bool :=
  decide (∀ (i : Fin seq.size), seq[i.val]!.size = seq[0]!.size)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def allSequenceEqualLength_postcond (seq : Array (Array Int)) (result: Bool) (h_precond : allSequenceEqualLength_precond seq) :=
  (∀ i j, i < seq.size → j < seq.size → seq[i]!.size = seq[j]!.size) ↔ result

theorem allSequenceEqualLength_spec_satisfied (seq: Array (Array Int)) (h_precond : allSequenceEqualLength_precond seq) :
    allSequenceEqualLength_postcond seq (allSequenceEqualLength seq h_precond) h_precond := by
  classical
unfold allSequenceEqualLength_postcond allSequenceEqualLength
have h0 : 0 < seq.size := h_precond
set Q : Prop := ∀ (i : Fin seq.size), seq[i.val]!.size = seq[0]!.size with hQdef
have hEquiv :
    (∀ i j, i < seq.size → j < seq.size → seq[i]!.size = seq[j]!.size) ↔ Q := by
  simpa [Q] using pairwise_eq_iff_all_eq_base (seq := seq) (h0 := h0)
have : Q ↔ (decide Q) := by
  by_cases h : Q
  · simp [Q, h]
  · simp [Q, h]
simpa [Q] using hEquiv.trans this
-- </vc-theorems>
