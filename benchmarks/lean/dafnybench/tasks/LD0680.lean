-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ReplaceBlanksWithChar (s : String) (ch : Char) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ReplaceBlanksWithChar_spec (s : String) (ch : Char) :
let v := ReplaceBlanksWithChar s ch
(v.length = s.length) ∧
(∀ i, 0 ≤ i ∧ i < s.length →
((s.get ⟨i⟩ = ' ' → v.get ⟨i⟩ = ch) ∧
(s.get ⟨i⟩ ≠ ' ' → v.get ⟨i⟩ = s.get ⟨i⟩))) :=
sorry
-- </vc-theorems>