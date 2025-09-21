-- <vc-preamble>
def IsLowerCase (c : Char) : Bool :=
97 ≤ c.toNat ∧ c.toNat ≤ 122
def IsUpperCase (c : Char) : Bool :=
65 ≤ c.toNat ∧ c.toNat ≤ 90
def IsLowerUpperPair (c : Char) (C : Char) : Bool :=
c.toNat = C.toNat + 32
def IsUpperLowerPair (C : Char) (c : Char) : Bool :=
C.toNat = c.toNat - 32
def ShiftMinus32 (c : Char) : Char :=
Char.ofNat ((c.toNat - 32) % 128)
def Shift32 (c : Char) : Char :=
Char.ofNat ((c.toNat + 32) % 128)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ToggleCase (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ToggleCase_spec (s : String) (v : String) :
v = ToggleCase s →
v.length = s.length ∧
(∀ i, 0 ≤ i ∧ i < s.length →
(if IsLowerCase (s.get ⟨i⟩) then
IsLowerUpperPair (s.get ⟨i⟩) (v.get ⟨i⟩)
else if IsUpperCase (s.get ⟨i⟩) then
IsUpperLowerPair (s.get ⟨i⟩) (v.get ⟨i⟩)
else v.get ⟨i⟩ = s.get ⟨i⟩)) :=
sorry
-- </vc-theorems>