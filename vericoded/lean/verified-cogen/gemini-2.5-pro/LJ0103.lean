import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isSubArray_precond (main : Array Int) (sub : Array Int) : Prop :=
  sub.size ≤ main.size
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this implementation.
-- </vc-helpers>

-- <vc-definitions>
def isSubArray (main : Array Int) (sub : Array Int) (h_precond : isSubArray_precond main sub) : Bool :=
    let n := main.size - sub.size
  (List.range (n + 1)).any (fun k =>
    (main.extract k (k + sub.size)).toList = sub.toList)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSubArray_postcond (main : Array Int) (sub : Array Int) (result : Bool) (h_precond : isSubArray_precond main sub) : Prop :=
  result = (∃ k l : Nat, 0 ≤ k ∧ k ≤ (main.size - sub.size) ∧ l = k + sub.size ∧ (main.extract k l).toList = sub.toList)

theorem isSubArray_spec_satisfied (main : Array Int) (sub : Array Int) (h_precond : isSubArray_precond main sub) :
    isSubArray_postcond main sub (isSubArray main sub h_precond) h_precond := by
    simp [isSubArray, isSubArray_postcond, List.any_eq_true, List.mem_range, Nat.lt_succ_iff]
-- </vc-theorems>
