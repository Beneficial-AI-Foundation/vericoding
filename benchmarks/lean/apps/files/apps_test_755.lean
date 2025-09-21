-- <vc-preamble>
def ValidInput (x : Int) : Prop :=
  x ≥ 1

def IsMinimalSteps (x : Int) (steps : Int) : Prop :=
  x ≥ 1 → (steps ≥ 1 ∧ steps * 5 ≥ x ∧ (steps - 1) * 5 < x)

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  ValidInput x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>