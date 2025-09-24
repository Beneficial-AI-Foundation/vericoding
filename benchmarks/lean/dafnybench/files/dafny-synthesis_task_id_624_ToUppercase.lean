-- <vc-preamble>
def IsLowerCase (c : Char) : Bool :=
97 ≤ c.toNat ∧ c.toNat ≤ 122
def IsLowerUpperPair (c : Char) (C : Char) : Bool :=
c.toNat = C.toNat + 32
def ShiftMinus32 (c : Char) : Char :=
Char.ofNat ((c.toNat - 32) % 128)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ToUppercase (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ToUppercase_spec (s : String) :
let v := ToUppercase s
v.length = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length →
(if IsLowerCase (s.get ⟨i⟩)
then IsLowerUpperPair (s.get ⟨i⟩) (v.get ⟨i⟩)
else v.get ⟨i⟩ = s.get ⟨i⟩) :=
sorry
-- </vc-theorems>