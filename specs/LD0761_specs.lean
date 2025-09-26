-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindFirstRepeatedChar (s : String) : Bool × Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindFirstRepeatedChar_spec (s : String) :
let (found, c) := FindFirstRepeatedChar s
(found → ∃ i j, 0 ≤ i ∧ i < j ∧ j < s.length ∧
s.get ⟨i⟩ = s.get ⟨j⟩ ∧ s.get ⟨i⟩ = c ∧
(∀ k l, 0 ≤ k ∧ k < l ∧ l < j ∧ s.get ⟨k⟩ = s.get ⟨l⟩ → k ≥ i)) ∧
(!found → ∀ i j, 0 ≤ i ∧ i < j ∧ j < s.length → s.get ⟨i⟩ ≠ s.get ⟨j⟩) :=
sorry
-- </vc-theorems>