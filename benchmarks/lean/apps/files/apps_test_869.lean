-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ b ≥ 1

def MaxDifferentDays (a b : Int) : Int :=
  if a < b then a else b

def RemainingAfterDifferent (a b : Int) : Int :=
  if a > b then a - MaxDifferentDays a b else b - MaxDifferentDays a b

def SameDays (a b : Int) : Int :=
  RemainingAfterDifferent a b / 2

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
def solve_postcond (a b : Int) (result: Int × Int) (h_precond : solve_precond a b) : Prop :=
  result.1 = MaxDifferentDays a b ∧
  result.2 = SameDays a b ∧
  result.1 ≥ 0 ∧
  result.2 ≥ 0 ∧
  result.1 ≤ a ∧ result.1 ≤ b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>