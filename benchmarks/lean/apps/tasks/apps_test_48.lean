-- <vc-preamble>
partial def countLessValue (n m target : Int) : Int :=
  if n = 0 then 0
  else 
    let maxJ := (target - 1) / n
    let actualMaxJ := if maxJ > m then m else maxJ
    let contribution := if actualMaxJ ≥ 1 then actualMaxJ else 0
    contribution + countLessValue (n - 1) m target

def countLessOrEqualValue (n m target : Int) : Int :=
  if target ≤ 0 then 0
  else if target ≥ n * m then n * m
  else countLessValue n m (target + 1)

def ValidInput (n m k : Int) : Prop :=
  1 ≤ n ∧ n ≤ 500000 ∧ 1 ≤ m ∧ m ≤ 500000 ∧ 1 ≤ k ∧ k ≤ n * m

@[reducible, simp]
def solve_precond (n m k : Int) : Prop :=
  ValidInput n m k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Int) (h_precond : solve_precond n m k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (result : Int) (h_precond : solve_precond n m k) : Prop :=
  1 ≤ result ∧ result ≤ n * m ∧
  countLessOrEqualValue n m result ≥ k ∧
  (result = 1 ∨ countLessOrEqualValue n m (result - 1) < k)

theorem solve_spec_satisfied (n m k : Int) (h_precond : solve_precond n m k) :
    solve_postcond n m k (solve n m k h_precond) h_precond := by
  sorry
-- </vc-theorems>