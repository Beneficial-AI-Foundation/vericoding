-- <vc-preamble>
def ValidInput (queries : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < queries.length → queries[i]! ≥ 2

def MinAdditionalMatches (n : Int) : Int :=
  if n ≥ 4 then n % 2 else 4 - n

def ValidResult (queries : List Int) (results : List Int) : Prop :=
  results.length = queries.length ∧
  ∀ i, 0 ≤ i ∧ i < queries.length → results[i]! = MinAdditionalMatches queries[i]!

@[reducible, simp]
def solve_precond (queries : List Int) : Prop :=
  ValidInput queries
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (queries : List Int) (h_precond : solve_precond queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (queries : List Int) (results : List Int) (h_precond : solve_precond queries) : Prop :=
  ValidResult queries results

theorem solve_spec_satisfied (queries : List Int) (h_precond : solve_precond queries) :
    solve_postcond queries (solve queries h_precond) h_precond := by
  sorry
-- </vc-theorems>