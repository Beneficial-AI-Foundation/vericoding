-- <vc-preamble>
def ValidInput (n : Int) (queries : List (Int × Int)) : Prop :=
  n > 0 ∧ 
  ∀ i, i < queries.length → 1 ≤ queries[i]!.1 ∧ queries[i]!.1 ≤ n ∧ 1 ≤ queries[i]!.2 ∧ queries[i]!.2 ≤ n

def ChessboardValue (n : Int) (x : Int) (y : Int) : Int :=
  if n > 0 ∧ 0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n then
    if (x + y) % 2 = 0 then
      1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    else
      (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
  else
    0

def ValidResult (n : Int) (queries : List (Int × Int)) (results : List Int) : Prop :=
  ValidInput n queries →
  results.length = queries.length ∧
  ∀ i, i < queries.length → 
    let x := queries[i]!.1 - 1
    let y := queries[i]!.2 - 1
    0 ≤ x ∧ x < n ∧ 0 ≤ y ∧ y < n ∧
    results[i]! = ChessboardValue n x y

@[reducible, simp]
def solve_precond (n : Int) (queries : List (Int × Int)) : Prop :=
  ValidInput n queries
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (queries : List (Int × Int)) (h_precond : solve_precond n queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (queries : List (Int × Int)) (results : List Int) (h_precond : solve_precond n queries) : Prop :=
  ValidResult n queries results

theorem solve_spec_satisfied (n : Int) (queries : List (Int × Int)) (h_precond : solve_precond n queries) :
    solve_postcond n queries (solve n queries h_precond) h_precond := by
  sorry
-- </vc-theorems>