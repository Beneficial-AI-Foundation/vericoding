-- <vc-preamble>

def SplitStringHelper (s : String) (i : Nat) (current : String) (acc : List String) : List String :=
  if h : i < s.length then
    let c := s.get (String.Pos.mk i)
    if c = ' ' ∨ c = '\n' ∨ c = '\t' then
      if current.length > 0 then
        SplitStringHelper s (i + 1) "" (acc ++ [current])
      else
        SplitStringHelper s (i + 1) "" acc
    else
      SplitStringHelper s (i + 1) (current ++ String.singleton c) acc
  else
    if current.length > 0 then acc ++ [current] else acc

def SplitStringPure (s : String) : List String :=
  SplitStringHelper s 0 "" []

def StringToIntHelperUnsigned (s : String) (i : Nat) (acc : Int) : Int :=
  if h : i < s.length then
    let c := s.get (String.Pos.mk i)
    if '0' ≤ c ∧ c ≤ '9' then
      StringToIntHelperUnsigned s (i + 1) (acc * 10 + Int.ofNat (c.toNat - '0'.toNat))
    else
      acc
  else
    acc

def StringToIntPure (s : String) : Int :=
  if h : s.length > 0 ∧ s.get (String.Pos.mk 0) = '-' then
    -(StringToIntHelperUnsigned s 1 0)
  else
    StringToIntHelperUnsigned s 0 0

def IsValidInteger (s : String) : Prop :=
  s.length > 0 ∧ (∀ i : Nat, i < s.length → 
    let c := s.get (String.Pos.mk i)
    ('0' ≤ c ∧ c ≤ '9') ∨ (i = 0 ∧ c = '-'))

def ValidParseable (input : String) : Prop :=
  let parts := SplitStringPure input
  parts.length ≥ 4

def AllPartsAreIntegers (input : String) : Prop :=
  let parts := SplitStringPure input
  parts.length ≥ 4 ∧
  IsValidInteger (parts[0]!) ∧
  IsValidInteger (parts[1]!) ∧
  IsValidInteger (parts[2]!) ∧
  IsValidInteger (parts[3]!)

def ValidParse (input : String) (a b c d : Int) : Prop :=
  let parts := SplitStringPure input
  parts.length ≥ 4 ∧
  IsValidInteger (parts[0]!) ∧
  IsValidInteger (parts[1]!) ∧
  IsValidInteger (parts[2]!) ∧
  IsValidInteger (parts[3]!) ∧
  StringToIntPure (parts[0]!) = a ∧
  StringToIntPure (parts[1]!) = b ∧
  StringToIntPure (parts[2]!) = c ∧
  StringToIntPure (parts[3]!) = d

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (∀ a b c d : Int, ValidParse input a b c d → 
    (result = "Left\n" ↔ a + b > c + d) ∧
    (result = "Right\n" ↔ a + b < c + d) ∧
    (result = "Balanced\n" ↔ a + b = c + d)) ∧
  (ValidParseable input ∧ AllPartsAreIntegers input → (result = "Left\n" ∨ result = "Right\n" ∨ result = "Balanced\n")) ∧
  (¬ValidParseable input ∨ ¬AllPartsAreIntegers input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>