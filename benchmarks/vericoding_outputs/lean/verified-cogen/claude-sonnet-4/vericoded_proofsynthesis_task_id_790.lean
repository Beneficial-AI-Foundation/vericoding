import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isEvenAtEvenIndex_precond (arr : Array Nat) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper function to check if index parity matches element parity
def checkParityMatch (arr : Array Nat) (i : Nat) : Bool :=
  if i < arr.size then (i % 2) = (arr[i]! % 2) else true

-- LLM HELPER: Helper function to check all indices
def allIndicesMatch (arr : Array Nat) : Bool :=
  (List.range arr.size).all (fun i => checkParityMatch arr i)
-- </vc-helpers>

-- <vc-definitions>
def isEvenAtEvenIndex (arr : Array Nat) (h_precond : isEvenAtEvenIndex_precond (arr)) : Bool :=
  (List.range arr.size).all (fun i => (i % 2) = (arr[i]! % 2))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isEvenAtEvenIndex_postcond (arr : Array Nat) (result: Bool) (h_precond : isEvenAtEvenIndex_precond (arr)) :=
  (∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2))) ↔ result

theorem isEvenAtEvenIndex_spec_satisfied (arr: Array Nat) (h_precond : isEvenAtEvenIndex_precond (arr)) :
    isEvenAtEvenIndex_postcond (arr) (isEvenAtEvenIndex (arr) h_precond) h_precond := by
  unfold isEvenAtEvenIndex_postcond isEvenAtEvenIndex
  constructor
  · intro h
    simp [List.all_eq_true]
    intro i hi
    exact h i hi
  · intro h
    intro i hi
    simp [List.all_eq_true] at h
    exact h i hi
-- </vc-theorems>

def main : IO Unit := return ()