-- <vc-preamble>
@[reducible, simp]
def findFirstOdd_precond (arr : Array UInt32) : Prop := True

@[reducible, simp]
def checkFindFirstOdd (arr : Array UInt32) (index : Option Nat) : Prop :=
  match index with
  | some idx => 
    (∀ i, i < idx → arr[i]! % 2 = 0) ∧ arr[idx]! % 2 ≠ 0
  | none => 
    ∀ k, k < arr.size → arr[k]! % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirstOdd (arr : Array UInt32) (h_precond : findFirstOdd_precond arr) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirstOdd_postcond (arr : Array UInt32) (index : Option Nat) (h_precond : findFirstOdd_precond arr) : Prop :=
  checkFindFirstOdd arr index

theorem findFirstOdd_spec_satisfied (arr : Array UInt32) (h_precond : findFirstOdd_precond arr) :
    findFirstOdd_postcond arr (findFirstOdd arr h_precond) h_precond := by
  sorry
-- </vc-theorems>