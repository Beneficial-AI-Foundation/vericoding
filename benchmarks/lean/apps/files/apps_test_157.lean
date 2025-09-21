-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ a ∧ a ≤ 1000 ∧ 1 ≤ b ∧ b ≤ 1000 ∧ 1 ≤ c ∧ c ≤ 1000

def MaxRecipeUnits (a b c : Int) : Int :=
  min a (min (b / 2) (c / 4))

def TotalFruitsUsed (units : Int) : Int :=
  units * 7

@[reducible, simp]
def solve_precond (a b c : Int) : Prop :=
  ValidInput a b c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c : Int) (h_precond : solve_precond a b c) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c : Int) (result : Int) (h_precond : solve_precond a b c) : Prop :=
  result = TotalFruitsUsed (MaxRecipeUnits a b c) ∧ result ≥ 0

theorem solve_spec_satisfied (a b c : Int) (h_precond : solve_precond a b c) :
    solve_postcond a b c (solve a b c h_precond) h_precond := by
  sorry
-- </vc-theorems>