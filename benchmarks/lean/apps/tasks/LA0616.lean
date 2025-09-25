-- <vc-preamble>
partial def ParseUnsignedInt (s : String) : Int :=
  if s.length = 0 then 0
  else ParseUnsignedInt (s.dropRight 1) * 10 + (s.back.toNat - '0'.toNat)

def ParseIntFunc (s : String) : Int :=
  if s.length > 0 ∧ s.get! 0 = '-' then
    -(ParseUnsignedInt (s.drop 1))
  else
    ParseUnsignedInt s

partial def SplitBySpacesHelper (s : String) (i : Nat) (current : String) (parts : List String) : List String :=
  if i ≥ s.length then
    if current.length > 0 then parts ++ [current] else parts
  else if s.get ⟨i⟩ = ' ' ∨ s.get ⟨i⟩ = '\n' ∨ s.get ⟨i⟩ = '\t' then
    if current.length > 0 then
      SplitBySpacesHelper s (i + 1) "" (parts ++ [current])
    else
      SplitBySpacesHelper s (i + 1) current parts
  else
    SplitBySpacesHelper s (i + 1) (current.push (s.get ⟨i⟩)) parts

def SplitBySpacesFunc (s : String) : List String :=
  SplitBySpacesHelper s 0 "" []

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧
  (s.get! 0 ≠ '-' ∨ s.length > 1) ∧
  (s.get! 0 = '-' → ∀ i, 1 ≤ i ∧ i < s.length → '0' ≤ s.get ⟨i⟩ ∧ s.get ⟨i⟩ ≤ '9') ∧
  (s.get! 0 ≠ '-' → ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.get ⟨i⟩ ∧ s.get ⟨i⟩ ≤ '9')

def ValidThreeIntegers (input : String) (a b c : Int) : Prop :=
  let parts := SplitBySpacesFunc input
  parts.length = 3 ∧
  (parts.length ≥ 1 → IsValidInteger (parts.get! 0)) ∧
  (parts.length ≥ 2 → IsValidInteger (parts.get! 1)) ∧
  (parts.length ≥ 3 → IsValidInteger (parts.get! 2)) ∧
  (parts.length ≥ 1 → ParseIntFunc (parts.get! 0) = a) ∧
  (parts.length ≥ 2 → ParseIntFunc (parts.get! 1) = b) ∧
  (parts.length ≥ 3 → ParseIntFunc (parts.get! 2) = c)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (_ : solve_precond input) : String :=
  ""
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  (∃ a b c : Int, ValidThreeIntegers input a b c) →
    (result = "YES\n" ∨ result = "NO\n") ∧
  (∃ a b c : Int, ValidThreeIntegers input a b c) →
    (∃ a b c : Int, ValidThreeIntegers input a b c ∧
      (result = "YES\n" ↔ b - a = c - b)) ∧
  (¬∃ a b c : Int, ValidThreeIntegers input a b c) →
    result = "" ∧
  (∀ a1 b1 c1 a2 b2 c2 : Int,
    ValidThreeIntegers input a1 b1 c1 ∧ ValidThreeIntegers input a2 b2 c2 →
    a1 = a2 ∧ b1 = b2 ∧ c1 = c2)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>