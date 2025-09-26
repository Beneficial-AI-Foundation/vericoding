import Mathlib
-- <vc-preamble>
def SetProduct (s : List Int) : Int :=
match s with
| [] => 1
| x::xs => x * SetProduct xs
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def UniqueProduct (arr : Array Int) : Int :=
SetProduct arr.toList
-- </vc-definitions>

-- <vc-theorems>
theorem UniqueProduct_spec (arr : Array Int) :
UniqueProduct arr = SetProduct (arr.toList) :=
rfl
-- </vc-theorems>
