-- <vc-preamble>
/- Helper functions for character manipulation -/

@[reducible, simp]
def isLowerCase (c : Char) : Bool :=
  c >= 'a' && c <= 'z'

@[reducible, simp]  
def shiftMinus32Spec (c : Char) : Char :=
  Char.ofNat (c.toNat - 32)

@[reducible, simp]
def innerExprToUppercase (str1 : Array Char) (i : Nat) : Char :=
  if isLowerCase str1[i]! then
    shiftMinus32Spec str1[i]!
  else
    str1[i]!

@[reducible, simp]
def toUppercase_precond (str1 : Array Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toUppercase (str1 : Array Char) (h_precond : toUppercase_precond str1) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def toUppercase_postcond (str1 : Array Char) (result : Array Char) (h_precond : toUppercase_precond str1) : Prop :=
  str1.size = result.size ∧ 
  (∀ i : Nat, i < str1.size → result[i]! = innerExprToUppercase str1 i)

theorem toUppercase_spec_satisfied (str1 : Array Char) (h_precond : toUppercase_precond str1) :
    toUppercase_postcond str1 (toUppercase str1 h_precond) h_precond := by
  sorry
-- </vc-theorems>