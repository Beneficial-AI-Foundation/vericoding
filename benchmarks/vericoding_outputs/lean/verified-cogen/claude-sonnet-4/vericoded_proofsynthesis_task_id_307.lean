import Mathlib
-- <vc-preamble>
-- <vc-preamble>
@[reducible, simp]
def listDeepClone_precond (arr : Array Nat) := 
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Use Array.map to create a proper clone
def Array.deepClone (arr : Array Nat) : Array Nat :=
  arr.map id

-- LLM HELPER  
lemma Array.size_deepClone (arr : Array Nat) : arr.size = arr.deepClone.size := by
  simp [Array.deepClone]

-- LLM HELPER
lemma Array.get_deepClone (arr : Array Nat) (i : Fin arr.size) : 
  arr.deepClone[i]! = arr[i]! := by
  simp [Array.deepClone]
-- </vc-helpers>

-- <vc-definitions>
def listDeepClone (arr : Array Nat) (h_precond : listDeepClone_precond (arr)) : Array Nat :=
  arr.deepClone
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def listDeepClone_postcond (arr : Array Nat) (copied: Array Nat) (h_precond : listDeepClone_precond (arr)) :=
  arr.size = copied.size ∧ (∀ i, i < arr.size → arr[i]! = copied[i]!)

theorem listDeepClone_spec_satisfied (arr: Array Nat) (h_precond : listDeepClone_precond (arr)) :
    listDeepClone_postcond (arr) (listDeepClone (arr) h_precond) h_precond := by
  -- Need to prove both size equality and element equality
  constructor
  · -- Prove size equality
    simp [listDeepClone]
    exact Array.size_deepClone arr
  · -- Prove element equality
    intro i hi
    simp [listDeepClone]
    have h_fin : i < arr.deepClone.size := by
      rw [← Array.size_deepClone]
      exact hi
    simp [Array.deepClone]
-- </vc-theorems>

def main : IO Unit := return ()