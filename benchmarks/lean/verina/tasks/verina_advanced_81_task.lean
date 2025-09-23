-- <vc-preamble>
@[reducible, simp]
def uniqueSorted_precond (arr : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueSorted (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def uniqueSorted_postcond (arr : List Int) (result: List Int) (h_precond : uniqueSorted_precond (arr)) : Prop :=
  List.isPerm arr.eraseDups result ∧ List.Pairwise (· ≤ ·) result

theorem uniqueSorted_spec_satisfied (arr: List Int) (h_precond : uniqueSorted_precond (arr)) :
    uniqueSorted_postcond (arr) (uniqueSorted (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>