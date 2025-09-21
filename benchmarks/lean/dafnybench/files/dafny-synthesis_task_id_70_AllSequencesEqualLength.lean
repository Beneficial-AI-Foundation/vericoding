-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AllSequencesEqualLength (sequences : Array (Array Int)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AllSequencesEqualLength_spec (sequences : Array (Array Int)) :
AllSequencesEqualLength sequences ↔
(∀ i j, 0 ≤ i ∧ i < sequences.size ∧ 0 ≤ j ∧ j < sequences.size →
(sequences[i]!).size = (sequences[j]!).size) :=
sorry
-- </vc-theorems>