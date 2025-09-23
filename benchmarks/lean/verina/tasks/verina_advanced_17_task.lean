-- <vc-preamble>
@[reducible]
def insertionSort_precond (l : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Helper function to insert an integer into a sorted list
def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

-- Helper function to sort a list using insertion sort
def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)
-- </vc-helpers>

-- <vc-definitions>
def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def insertionSort_postcond (l : List Int) (result: List Int) (h_precond : insertionSort_precond (l)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result

theorem insertionSort_spec_satisfied (l: List Int) (h_precond : insertionSort_precond (l)) :
    insertionSort_postcond (l) (insertionSort (l) h_precond) h_precond := by
  sorry
-- </vc-theorems>