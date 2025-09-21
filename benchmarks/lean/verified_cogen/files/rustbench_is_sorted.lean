-- <vc-preamble>
@[reducible, simp]
def isSorted_precond (lst : Array Int) :=
  lst.size ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (lst : Array Int) (h_precond : isSorted_precond lst) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSorted_postcond (lst : Array Int) (result : Bool) (h_precond : isSorted_precond lst) :=
  (result → ∀ i j, 0 ≤ i ∧ i < j ∧ j < lst.size → lst[i]! ≤ lst[j]!) ∧
  (¬result → ∃ i j, 0 ≤ i ∧ i < j ∧ j < lst.size ∧ lst[i]! > lst[j]!)

theorem isSorted_spec_satisfied (lst : Array Int) (h_precond : isSorted_precond lst) :
    isSorted_postcond lst (isSorted lst h_precond) h_precond := by
  sorry
-- </vc-theorems>