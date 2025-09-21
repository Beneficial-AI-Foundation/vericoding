-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  k ≥ 1 ∧ n ≥ 1 ∧ k ≤ n

def TotalMoves (n k : Int) (h : ValidInput n k) : Int :=
  n / k

def FirstPlayerWins (n k : Int) (h : ValidInput n k) : Prop :=
  TotalMoves n k h % 2 = 1

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : String) (h_precond : solve_precond n k) : Prop :=
  (FirstPlayerWins n k h_precond → result = "YES") ∧
  (¬FirstPlayerWins n k h_precond → result = "NO")

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>