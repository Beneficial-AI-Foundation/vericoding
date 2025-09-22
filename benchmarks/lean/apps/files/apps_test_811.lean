-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ a ≤ 1000 ∧ b ≥ 2 ∧ b ≤ 1000

partial def TotalBurningHours (a b : Int) : Int :=
  if a = 0 then 0
  else if a < b then a
  else a + TotalBurningHours (a / b) b

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
  result ≥ a ∧ result = TotalBurningHours a b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>