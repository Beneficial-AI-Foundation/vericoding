-- <vc-preamble>
def IsComposite (x : Int) : Prop :=
  x ≥ 4 ∧ ∃ k, 2 ≤ k ∧ k < x ∧ x % k = 0

def ValidInput (queries : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < queries.length → queries[i]! ≥ 1

def MaxCompositeSummands (n : Int) : Int :=
  if n % 4 = 0 then n / 4
  else if n % 4 = 1 ∧ n / 4 ≥ 2 then n / 4 - 1
  else if n % 4 = 2 ∧ n / 4 ≥ 1 then n / 4
  else if n % 4 = 3 ∧ n / 4 ≥ 3 then n / 4 - 1
  else -1

def ValidResult (queries : List Int) (results : List Int) : Prop :=
  results.length = queries.length ∧
  (∀ i, 0 ≤ i ∧ i < queries.length → results[i]! = MaxCompositeSummands queries[i]!) ∧
  (∀ i, 0 ≤ i ∧ i < queries.length → results[i]! ≥ -1)

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