import Mathlib
-- <vc-preamble>
@[reducible, simp]
def elementWiseModule_precond (arr1 : Array Int) (arr2 : Array Int) :=
  arr1.size = arr2.size ∧ (∀ i, i < arr2.size → arr2[i]! ≠ 0) ∧ (∀ i, i < arr1.size → Int.emod arr1[i]! arr2[i]! ≥ Int.negSucc 2147483647 ∧ Int.emod arr1[i]! arr2[i]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Array mapping with index for element-wise operations
def Array.mapIdx2 {α β γ : Type*} [Inhabited α] [Inhabited β] (f : Nat → α → β → γ) (arr1 : Array α) (arr2 : Array β) : Array γ :=
  Array.ofFn (fun i : Fin arr1.size => f i.val arr1[i]! arr2[i]!)
-- </vc-helpers>

-- <vc-definitions>
def elementWiseModule (arr1 : Array Int) (arr2 : Array Int) (h_precond : elementWiseModule_precond arr1 arr2) : Array Int :=
  Array.ofFn (fun i : Fin arr1.size => Int.emod arr1[i]! arr2[i]!)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def elementWiseModule_postcond (arr1 : Array Int) (arr2 : Array Int) (result: Array Int) (h_precond : elementWiseModule_precond arr1 arr2) :=
  result.size = arr1.size ∧ (∀ i, i < result.size → result[i]! = Int.emod arr1[i]! arr2[i]!)

theorem elementWiseModule_spec_satisfied (arr1: Array Int) (arr2: Array Int) (h_precond : elementWiseModule_precond arr1 arr2) :
    elementWiseModule_postcond arr1 arr2 (elementWiseModule arr1 arr2 h_precond) h_precond := by
  unfold elementWiseModule_postcond elementWiseModule
  constructor
  · simp [Array.size_ofFn]
  · intro i hi
    simp at hi
    simp [Array.getElem_ofFn, hi]
-- </vc-theorems>

def main : IO Unit := do
  return ()