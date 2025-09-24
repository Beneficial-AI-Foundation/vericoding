-- <vc-preamble>
def ValidInput (H A : Int) : Prop :=
  H ≥ 1 ∧ A ≥ 1

def IsMinimumAttacks (attacks H A : Int) : Prop :=
  attacks ≥ 1 ∧
  attacks * A ≥ H ∧
  (attacks - 1) * A < H

def CeilDiv (H A : Int) : Int :=
  (H + A - 1) / A

@[reducible, simp]
def solve_precond (H A : Int) : Prop :=
  ValidInput H A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (H A : Int) (h_precond : solve_precond H A) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (H A : Int) (attacks : Int) (h_precond : solve_precond H A) : Prop :=
  IsMinimumAttacks attacks H A ∧ attacks = CeilDiv H A

theorem solve_spec_satisfied (H A : Int) (h_precond : solve_precond H A) :
    solve_postcond H A (solve H A h_precond) h_precond := by
  sorry
-- </vc-theorems>