-- <vc-preamble>
def IsUpperCase (c : Char) : Bool :=
65 ≤ c.toNat ∧ c.toNat ≤ 90
def IsUpperLowerPair (C : Char) (c : Char) : Bool :=
C.toNat = c.toNat - 32
def Shift32 (c : Char) : Char :=
Char.ofNat ((c.toNat + 32) % 128)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ToLowercase (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ToLowercase_spec (s : String) :
let v := ToLowercase s
v.length = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length →
(if IsUpperCase (s.get ⟨i⟩)
then IsUpperLowerPair (s.get ⟨i⟩) (v.get ⟨i⟩)
else v.get ⟨i⟩ = s.get ⟨i⟩) :=
sorry
-- </vc-theorems>