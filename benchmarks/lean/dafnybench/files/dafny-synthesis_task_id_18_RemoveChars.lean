-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RemoveChars (s1 s2 : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RemoveChars_spec (s1 s2 : String) :
let v := RemoveChars s1 s2
(v.length ≤ s1.length) ∧
(∀ i, 0 ≤ i ∧ i < v.length →
(v.get ⟨i⟩ ∈ s1.data) ∧ ¬(v.get ⟨i⟩ ∈ s2.data)) ∧
(∀ i, 0 ≤ i ∧ i < s1.length →
(s1.get ⟨i⟩ ∈ s2.data) ∨ (s1.get ⟨i⟩ ∈ v.data)) :=
sorry
-- </vc-theorems>