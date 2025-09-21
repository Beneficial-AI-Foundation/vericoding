-- <vc-preamble>
@[reducible, simp]
def isSorted_precond (arr : Array Int) :=
  arr.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (arr : Array Int) (h_precond : isSorted_precond (arr)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isSorted_postcond (arr : Array Int) (is_sorted: Bool) (h_precond : isSorted_precond (arr)) :=
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr[i]! ≤ arr[j]!) ↔ is_sorted

theorem isSorted_spec_satisfied (arr: Array Int) (h_precond : isSorted_precond (arr)) :
    isSorted_postcond (arr) (isSorted (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>