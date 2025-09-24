-- <vc-preamble>
@[reducible, simp]
def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b
-- </vc-preamble>

-- <vc-helpers>
def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged
-- </vc-helpers>

-- <vc-definitions>
def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) (h_precond : mergeSorted_precond (a) (b)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)

theorem mergeSorted_spec_satisfied (a: List Int) (b: List Int) (h_precond : mergeSorted_precond (a) (b)) :
    mergeSorted_postcond (a) (b) (mergeSorted (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>