-- <vc-preamble>
@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

theorem insertionSort_spec_satisfied (xs: List Int) (h_precond : insertionSort_precond (xs)) :
    insertionSort_postcond (xs) (insertionSort (xs) h_precond) h_precond := by
  sorry
-- </vc-theorems>