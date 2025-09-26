import Mathlib
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

-- <vc-definitions>
def toToggleCase (str1 : Array Char) (h_precond : toToggleCase_precond (str1)) : Array Char :=
  str1.map toToggleCaseSpec
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def toToggleCase_postcond (str1 : Array Char) (toggleCase : Array Char) (h_precond : toToggleCase_precond (str1)) : Prop :=
  str1.size = toggleCase.size ∧
  (∀ i, i < str1.size → toggleCase[i]! = toToggleCaseSpec (str1[i]!))

theorem toToggleCase_spec_satisfied (str1 : Array Char) (h_precond : toToggleCase_precond (str1)) :
    toToggleCase_postcond (str1) (toToggleCase (str1) h_precond) h_precond := by
  unfold toToggleCase_postcond
  dsimp [toToggleCase]
  constructor
  · simp [Array.size_map]
  · intro i h
    simp [h]
-- </vc-theorems>
