-- <vc-preamble>
@[reducible, simp]
def mergeSort_precond (list : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeSort (list : List Int) (h_precond : mergeSort_precond (list)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def mergeSort_postcond (list : List Int) (result: List Int) (h_precond : mergeSort_precond (list)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm list result

theorem mergeSort_spec_satisfied (list: List Int) (h_precond : mergeSort_precond (list)) :
    mergeSort_postcond (list) (mergeSort (list) h_precond) h_precond := by
  sorry
-- </vc-theorems>