-- <vc-preamble>
def ValidQuery (k n a b : Int) : Prop :=
  k > 0 ∧ n > 0 ∧ a > 0 ∧ b > 0 ∧ b < a

def MaxActionATurns (k n a b : Int) (h : ValidQuery k n a b) : Int :=
  if n * b > k then 
    -1
  else 
    let maxPossible := (k - n * b - 1) / (a - b)
    if n ≤ maxPossible then n else maxPossible

def ValidResult (result k n a b : Int) (h : ValidQuery k n a b) : Prop :=
  result = -1 ∨ (0 ≤ result ∧ result ≤ n)

@[reducible, simp]
def solve_precond (queries : List (Int × Int × Int × Int)) : Prop :=
  queries.length > 0 ∧ 
  ∀ i, 0 ≤ i ∧ i < queries.length → 
    let (k, n, a, b) := queries[i]!
    ValidQuery k n a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (queries : List (Int × Int × Int × Int)) (h_precond : solve_precond queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (queries : List (Int × Int × Int × Int)) (results : List Int) (h_precond : solve_precond queries) : Prop :=
  results.length = queries.length ∧
  (∀ i, 0 ≤ i ∧ i < queries.length → 
    let (k, n, a, b) := queries[i]!
    have h_valid : ValidQuery k n a b := by sorry
    results[i]! = MaxActionATurns k n a b h_valid) ∧
  (∀ i, 0 ≤ i ∧ i < results.length → 
    let (k, n, a, b) := queries[i]!
    have h_valid : ValidQuery k n a b := by sorry
    ValidResult results[i]! k n a b h_valid)

theorem solve_spec_satisfied (queries : List (Int × Int × Int × Int)) (h_precond : solve_precond queries) :
    solve_postcond queries (solve queries h_precond) h_precond := by
  sorry
-- </vc-theorems>