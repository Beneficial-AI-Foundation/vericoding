import Mathlib
-- <vc-preamble>
@[reducible, simp]
def findEvenNumbers_precond (arr : Array Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Use existing Array.filter from Mathlib
-- No additional helpers needed since Array.filter and related theorems already exist
-- </vc-helpers>

-- <vc-definitions>
def findEvenNumbers (arr : Array Nat) (h_precond : findEvenNumbers_precond (arr)) : Array Nat :=
  arr.filter (fun x => x % 2 = 0)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Nat) (even_numbers: Array Nat) (h_precond : findEvenNumbers_precond (arr)) :=
  even_numbers.toList = arr.toList.filter (fun x => x % 2 = 0)

theorem findEvenNumbers_spec_satisfied (arr: Array Nat) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
  simp [findEvenNumbers_postcond, findEvenNumbers]
-- </vc-theorems>

def main : IO Unit := do
  pure ()