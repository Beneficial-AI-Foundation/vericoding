-- <vc-preamble>
@[reducible, simp]
def isSubList_precond (main : Array Int) (sub : Array Int) : Prop :=
  sub.size ≤ main.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubList (main : Array Int) (sub : Array Int) (h_precond : isSubList_precond main sub) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSubList_postcond (main : Array Int) (sub : Array Int) (result : Bool) (h_precond : isSubList_precond main sub) : Prop :=
  result = (∃ k l : Nat, 0 ≤ k ∧ k ≤ (main.size - sub.size) ∧ l = k + sub.size ∧ 
    (∀ i, i < sub.size → main[k + i]! = sub[i]!))

theorem isSubList_spec_satisfied (main : Array Int) (sub : Array Int) (h_precond : isSubList_precond main sub) :
    isSubList_postcond main sub (isSubList main sub h_precond) h_precond := by
  sorry
-- </vc-theorems>