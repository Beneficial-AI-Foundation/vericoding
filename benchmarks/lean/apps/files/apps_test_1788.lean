-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  -100 ≤ a ∧ a ≤ 100 ∧ -100 ≤ b ∧ b ≤ 100 ∧ (a + b) % 2 = 0 ∧ (a - b) % 2 = 0

def CorrectSolution (a b x y : Int) : Prop :=
  a = x + y ∧ b = x - y

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int × Int) (h_precond : solve_precond a b) : Prop :=
  CorrectSolution a b result.1 result.2

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>