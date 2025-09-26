-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ReplaceChars (s : String) (oldChar : Char) (newChar : Char) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ReplaceChars_spec (s : String) (oldChar newChar : Char) :
let v := ReplaceChars s oldChar newChar
v.length = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length →
((s.get ⟨i⟩ = oldChar → v.get ⟨i⟩ = newChar) ∧
(s.get ⟨i⟩ ≠ oldChar → v.get ⟨i⟩ = s.get ⟨i⟩)) :=
sorry
-- </vc-theorems>