-- <vc-preamble>
def ValidInput (scores : List Int) : Prop :=
  scores.length > 0 ∧ scores.length ≤ 100 ∧
  ∀ i, 0 ≤ i ∧ i < scores.length → 1 ≤ scores[i]! ∧ scores[i]! ≤ 100

def sum (scores : List Int) : Int :=
  scores.foldl (· + ·) 0

def AllMultiplesOf10 (scores : List Int) : Bool :=
  scores.all (fun x => x % 10 = 0)

def IsSmallestNonMultiple (scores : List Int) (value : Int) : Prop :=
  value ∈ scores ∧ 
  value % 10 ≠ 0 ∧
  ∀ x, x ∈ scores ∧ x % 10 ≠ 0 → value ≤ x

def CorrectResult (scores : List Int) (result : Int) : Prop :=
  let totalSum := sum scores
  if totalSum % 10 ≠ 0 then
    result = totalSum
  else if AllMultiplesOf10 scores then
    result = 0
  else
    ∃ smallestNonMultiple, 
      IsSmallestNonMultiple scores smallestNonMultiple ∧
      result = totalSum - smallestNonMultiple

@[reducible, simp]
def solve_precond (scores : List Int) : Prop :=
  ValidInput scores
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (scores : List Int) (h_precond : solve_precond scores) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (scores : List Int) (result : Int) (h_precond : solve_precond scores) : Prop :=
  CorrectResult scores result

theorem solve_spec_satisfied (scores : List Int) (h_precond : solve_precond scores) :
    solve_postcond scores (solve scores h_precond) h_precond := by
  sorry
-- </vc-theorems>