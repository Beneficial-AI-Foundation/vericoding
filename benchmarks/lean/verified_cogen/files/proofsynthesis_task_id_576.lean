-- <vc-preamble>
@[reducible, simp]
def isSubArray_precond (main : Array Int) (sub : Array Int) : Prop :=
  sub.size ≤ main.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubArray (main : Array Int) (sub : Array Int) (h_precond : isSubArray_precond main sub) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSubArray_postcond (main : Array Int) (sub : Array Int) (result : Bool) (h_precond : isSubArray_precond main sub) : Prop :=
  result = (∃ k l : Nat, 0 ≤ k ∧ k ≤ (main.size - sub.size) ∧ l = k + sub.size ∧ (main.extract k l).toList = sub.toList)

theorem isSubArray_spec_satisfied (main : Array Int) (sub : Array Int) (h_precond : isSubArray_precond main sub) :
    isSubArray_postcond main sub (isSubArray main sub h_precond) h_precond := by
  sorry
-- </vc-theorems>