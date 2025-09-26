import Mathlib
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
-- LLM HELPER
/-- Compute ceiling division by 5 for Int. For positive x this yields the minimal number of 5-sized steps
    required to cover x (i.e. ceil (x / 5)). -/
@[reducible, simp]
def ceil_div5 (x : Int) : Int := (x + 4) / 5

/-- Lightweight alias used for readability in the implementation. -/
@[reducible, simp]
def steps_for (x : Int) : Int := ceil_div5 x

-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  let steps := (x + 4) / 5
  steps
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
