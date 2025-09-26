import Mathlib
-- <vc-preamble>
def SetProduct (s : List Int) : Int :=
match s with
| [] => 1
| x::xs => x * SetProduct xs
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem SetProduct_nil : SetProduct [] = (1 : Int) := rfl
@[simp] theorem SetProduct_cons (x : Int) (xs : List Int) :
  SetProduct (x :: xs) = x * SetProduct xs := rfl
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
