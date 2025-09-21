-- <vc-preamble>
def IsSpaceCommaDot (c : Char) : Bool :=
c == ' ' ∨ c == ',' ∨ c == '.'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ReplaceWithColon (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ReplaceWithColon_spec (s : String) :
let v := ReplaceWithColon s
v.length = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length →
((IsSpaceCommaDot (s.get ⟨i⟩) → v.get ⟨i⟩ = ':') ∧
(¬IsSpaceCommaDot (s.get ⟨i⟩) → v.get ⟨i⟩ = s.get ⟨i⟩)) :=
sorry
-- </vc-theorems>