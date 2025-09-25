-- <vc-preamble>
def SetProduct (s : List Int) : Int :=
match s with
| [] => 1
| x::xs => x * SetProduct xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def UniqueProduct (arr : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem UniqueProduct_spec (arr : Array Int) :
UniqueProduct arr = SetProduct (arr.toList) :=
sorry
-- </vc-theorems>