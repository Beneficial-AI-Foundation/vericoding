-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ a ≤ 1000 ∧ b ≥ 1 ∧ b ≤ 1000 ∧ a ≠ b

def OptimalMeetingPoint (a b : Int) : Int :=
  (a + b) / 2

def tirednessForSteps (steps : Int) : Int :=
  if steps ≤ 0 then 0 else steps * (steps + 1) / 2

def MinimumTotalTiredness (a b : Int) (h : ValidInput a b) : Int :=
  let c := OptimalMeetingPoint a b
  tirednessForSteps (Int.natAbs (c - a)) + tirednessForSteps (Int.natAbs (b - c))

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result ≥ 0 ∧ result = MinimumTotalTiredness a b h_precond

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>