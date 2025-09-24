-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AllCharactersSame (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AllCharactersSame_spec (s : String) :
let result := AllCharactersSame s
(result → ∀ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length → s.get ⟨i⟩ = s.get ⟨j⟩) ∧
(!result → s.length > 1 ∧ ∃ i j, 0 ≤ i ∧ i < s.length ∧ 0 ≤ j ∧ j < s.length ∧ i ≠ j ∧ s.get ⟨i⟩ ≠ s.get ⟨j⟩) :=
sorry
-- </vc-theorems>