-- <vc-preamble>
def ValidInput (k2 k3 k5 k6 : Int) : Prop :=
  k2 ≥ 0 ∧ k3 ≥ 0 ∧ k5 ≥ 0 ∧ k6 ≥ 0 ∧
  k2 ≤ 5000000 ∧ k3 ≤ 5000000 ∧ k5 ≤ 5000000 ∧ k6 ≤ 5000000

def OptimalSum (k2 k3 k5 k6 : Int) (h : ValidInput k2 k3 k5 k6) : Int :=
  let count256 := min (min k2 k5) k6
  let remaining_k2 := k2 - count256
  let count32 := min k3 remaining_k2
  256 * count256 + 32 * count32

@[reducible, simp]
def solve_precond (k2 k3 k5 k6 : Int) : Prop :=
  ValidInput k2 k3 k5 k6
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k2 k3 k5 k6 : Int) (h_precond : solve_precond k2 k3 k5 k6) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k2 k3 k5 k6 : Int) (result : Int) (h_precond : solve_precond k2 k3 k5 k6) : Prop :=
  result ≥ 0 ∧ result = OptimalSum k2 k3 k5 k6 h_precond

theorem solve_spec_satisfied (k2 k3 k5 k6 : Int) (h_precond : solve_precond k2 k3 k5 k6) :
    solve_postcond k2 k3 k5 k6 (solve k2 k3 k5 k6 h_precond) h_precond := by
  sorry
-- </vc-theorems>