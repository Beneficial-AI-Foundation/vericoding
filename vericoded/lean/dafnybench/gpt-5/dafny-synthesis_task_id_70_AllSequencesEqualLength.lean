import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem decide_iff_toProp (p : Prop) [Decidable p] : (decide p = true) ↔ p := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]

-- </vc-helpers>

-- <vc-definitions>
def AllSequencesEqualLength (sequences : Array (Array Int)) : Bool :=
decide (∀ i j : Fin sequences.size,
    (sequences[i.val]!).size = (sequences[j.val]!).size)
-- </vc-definitions>

-- <vc-theorems>
theorem AllSequencesEqualLength_spec (sequences : Array (Array Int)) :
AllSequencesEqualLength sequences ↔
(∀ i j, 0 ≤ i ∧ i < sequences.size ∧ 0 ≤ j ∧ j < sequences.size →
(sequences[i]!).size = (sequences[j]!).size) :=
by
  classical
  let Q : Prop :=
    ∀ i j : Fin sequences.size,
      (sequences[i.val]!).size = (sequences[j.val]!).size
  let P : Prop :=
    ∀ i j, 0 ≤ i ∧ i < sequences.size ∧ 0 ≤ j ∧ j < sequences.size →
      (sequences[i]!).size = (sequences[j]!).size
  have hQ : ((AllSequencesEqualLength sequences) : Prop) ↔ Q := by
    simpa [AllSequencesEqualLength, Q] using (decide_iff_toProp Q)
  have hPQ : Q ↔ P := by
    constructor
    · intro hQ' i j hij
      rcases hij with ⟨hi0, h⟩
      rcases h with ⟨hi_lt, h'⟩
      rcases h' with ⟨hj0, hj_lt⟩
      simpa using hQ' ⟨i, hi_lt⟩ ⟨j, hj_lt⟩
    · intro hP' fi fj
      have hi0 : 0 ≤ fi.val := Nat.zero_le _
      have hj0 : 0 ≤ fj.val := Nat.zero_le _
      simpa using hP' fi.val fj.val ⟨hi0, fi.isLt, hj0, fj.isLt⟩
  exact hQ.trans hPQ
-- </vc-theorems>
