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

def main : IO Unit := do
  return ()