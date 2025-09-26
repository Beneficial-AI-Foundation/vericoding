import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  0 ≤ a ∧ a ≤ b

def XorInt (x y : Int) : Int :=
  0

def XorRange (a b : Int) : Int :=
  0

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  XorRange a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result = XorRange a b ∧ result ≥ 0

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve XorRange
  simp
-- </vc-theorems>
