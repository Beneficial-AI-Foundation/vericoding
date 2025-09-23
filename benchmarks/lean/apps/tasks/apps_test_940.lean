-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100

def IsTriangle (a b c : Int) : Prop :=
  a + b > c ∧ a + c > b ∧ b + c > a

def MinOperationsNeeded (a b c : Int) (h : ValidInput a b c) : Int :=
  let max_val := max (max a b) c
  let sum_of_other_two := a + b + c - max_val
  max 0 (max_val - sum_of_other_two + 1)

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
def solve_postcond (a b c : Int) (result: Int) (h_precond : solve_precond a b c) : Prop :=
  result ≥ 0 ∧ result = MinOperationsNeeded a b c h_precond ∧ (result = 0 ↔ IsTriangle a b c)

theorem solve_spec_satisfied (a b c : Int) (h_precond : solve_precond a b c) :
    solve_postcond a b c (solve a b c h_precond) h_precond := by
  sorry
-- </vc-theorems>