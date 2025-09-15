-- <vc-preamble>
/- Function to check if a character is upper case -/
@[reducible, simp]
def isUpperCase (c : Char) : Bool :=
  c >= 'A' ∧ c <= 'Z'

/- Function to shift character by 32 (upper to lower) -/
@[reducible, simp]
def shift32Spec (c : Char) : Char :=
  Char.ofNat ((c.toNat) + 32)

/- Function to check if a character is lower case -/
@[reducible, simp]
def isLowerCase (c : Char) : Bool :=
  c >= 'a' ∧ c <= 'z'

/- Function to shift character by -32 (lower to upper) -/
@[reducible, simp]
def shiftMinus32Spec (c : Char) : Char :=
  Char.ofNat ((c.toNat) - 32)

/- Function to toggle case of a character -/
@[reducible, simp]
def toToggleCaseSpec (s : Char) : Char :=
  if isLowerCase s then
    shiftMinus32Spec s
  else if isUpperCase s then
    shift32Spec s
  else
    s

/- Precondition for toToggleCase function -/
@[reducible, simp]
def toToggleCase_precond (str1 : Array Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()