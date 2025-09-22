-- <vc-preamble>
@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  ∀ i j, i < j → j < arr.size → arr[i]! ≤ arr[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond arr target) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (index : Option Nat) (h_precond : findFirstOccurrence_precond arr target) : Prop :=
  match index with
  | some idx => idx < arr.size ∧ (∀ k, k < idx → arr[k]! ≠ target) ∧ arr[idx]! = target
  | none => ∀ k, k < arr.size → arr[k]! ≠ target

theorem findFirstOccurrence_spec_satisfied (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond arr target) :
    findFirstOccurrence_postcond arr target (findFirstOccurrence arr target h_precond) h_precond := by
  sorry
-- </vc-theorems>