-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindAllOccurrences (text pattern : String) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindAllOccurrences_spec (text pattern : String) :
let offsets := FindAllOccurrences text pattern
(∀ i : Nat, i ∈ offsets → i + pattern.length ≤ text.length) ∧
(∀ i : Nat, i ≤ text.length - pattern.length →
(i ∈ offsets → (∀ j : Nat, j < pattern.length → text.get ⟨i + j⟩ = pattern.get ⟨j⟩)) ∧
((∀ j : Nat, j < pattern.length → text.get ⟨i + j⟩ = pattern.get ⟨j⟩) → i ∈ offsets)) :=
sorry
-- </vc-theorems>