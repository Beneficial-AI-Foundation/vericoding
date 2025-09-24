-- <vc-preamble>
def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n + 1 => base * pow base n

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ 10
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (years : Int) (h_precond : solve_precond a b) : Prop :=
  years ≥ 0 ∧ 
  a * pow 3 years.natAbs > b * pow 2 years.natAbs ∧ 
  (years = 0 ∨ a * pow 3 (years - 1).natAbs ≤ b * pow 2 (years - 1).natAbs)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>