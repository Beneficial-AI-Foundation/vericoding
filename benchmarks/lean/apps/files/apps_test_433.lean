-- <vc-preamble>
def ValidInput (n a b : Int) : Prop :=
  n ≥ 1 ∧ 1 ≤ a ∧ a ≤ n ∧ -100 ≤ b ∧ b ≤ 100

def FinalEntrance (n a b : Int) (h : ValidInput n a b) : Int :=
  ((a - 1 + b) % n + n) % n + 1

def ValidOutput (result n : Int) : Prop :=
  1 ≤ result ∧ result ≤ n

@[reducible, simp]
def solve_precond (n a b : Int) : Prop :=
  ValidInput n a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b : Int) (h_precond : solve_precond n a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b : Int) (result : Int) (h_precond : solve_precond n a b) : Prop :=
  ValidOutput result n ∧ result = FinalEntrance n a b h_precond

theorem solve_spec_satisfied (n a b : Int) (h_precond : solve_precond n a b) :
    solve_postcond n a b (solve n a b h_precond) h_precond := by
  sorry
-- </vc-theorems>