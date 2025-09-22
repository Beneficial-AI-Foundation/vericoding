-- <vc-preamble>
@[reducible]
def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeSortedLists (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result

theorem mergeSortedLists_spec_satisfied (arr1: List Int) (arr2: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    mergeSortedLists_postcond (arr1) (arr2) (mergeSortedLists (arr1) (arr2) h_precond) h_precond := by
  sorry
-- </vc-theorems>