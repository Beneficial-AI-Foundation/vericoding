-- <vc-preamble>
def ValidInput (n : Int) (scores : List Int) : Prop :=
  n = scores.length ∧ n ≥ 1 ∧ ∃ i, 0 ≤ i ∧ i < scores.length ∧ scores[i]! ≠ 0

def UniqueNonZeroScores (scores : List Int) : Nat :=
  (scores.filter (fun x => x ≠ 0)).eraseDups.length

def ValidResult (scores : List Int) (result : Int) : Prop :=
  result ≥ 1 ∧ result = UniqueNonZeroScores scores ∧ result ≤ scores.length

@[reducible, simp]
def solve_precond (n : Int) (scores : List Int) : Prop :=
  ValidInput n scores
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (scores : List Int) (h_precond : solve_precond n scores) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (scores : List Int) (result : Int) (h_precond : solve_precond n scores) : Prop :=
  ValidResult scores result

theorem solve_spec_satisfied (n : Int) (scores : List Int) (h_precond : solve_precond n scores) :
    solve_postcond n scores (solve n scores h_precond) h_precond := by
  sorry
-- </vc-theorems>