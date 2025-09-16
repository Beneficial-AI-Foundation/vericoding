

/-!
{
"name": "dafny-synthesis_task_id_624_ToUppercase",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_624_ToUppercase",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate indicating if a character is lowercase -/
def IsLowerCase (c : Char) : Bool :=
97 ≤ c.toNat ∧ c.toNat ≤ 122

/-- Predicate indicating if two characters form a lowercase-uppercase pair -/
def IsLowerUpperPair (c : Char) (C : Char) : Bool :=
c.toNat = C.toNat + 32

/-- Function that shifts a character's ASCII value by -32 -/
def ShiftMinus32 (c : Char) : Char :=
Char.ofNat ((c.toNat - 32) % 128)

/-- Main ToUppercase function that converts a string to uppercase -/
def ToUppercase (s : String) : String :=
sorry

/-- Specification for ToUppercase function -/
theorem ToUppercase_spec (s : String) :
let v := ToUppercase s
v.length = s.length ∧
∀ i, 0 ≤ i ∧ i < s.length →
(if IsLowerCase (s.get ⟨i⟩)
then IsLowerUpperPair (s.get ⟨i⟩) (v.get ⟨i⟩)
else v.get ⟨i⟩ = s.get ⟨i⟩) := sorry
