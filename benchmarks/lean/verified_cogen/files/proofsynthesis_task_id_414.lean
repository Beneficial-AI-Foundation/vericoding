-- <vc-preamble>
@[reducible, simp]
def anyValueExists_precond (arr1 : Array Int) (arr2 : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def anyValueExists (arr1 : Array Int) (arr2 : Array Int) (h_precond : anyValueExists_precond arr1 arr2) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def anyValueExists_postcond (arr1 : Array Int) (arr2 : Array Int) (result: Bool) (h_precond : anyValueExists_precond arr1 arr2) :=
  (∃ k, 0 ≤ k ∧ k < arr1.size ∧ arr2.toList.contains (arr1[k]!)) ↔ result

theorem anyValueExists_spec_satisfied (arr1: Array Int) (arr2: Array Int) (h_precond : anyValueExists_precond arr1 arr2) :
    anyValueExists_postcond arr1 arr2 (anyValueExists arr1 arr2 h_precond) h_precond := by
  sorry
-- </vc-theorems>