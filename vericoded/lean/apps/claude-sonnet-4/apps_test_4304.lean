import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ b > a ∧ b < 499500

def ValidSnowDepth (a b depth : Int) : Prop :=
  depth ≥ 1 ∧
  ((b - a) * (b - a) - (a + b)) ≥ 2 ∧
  ((b - a) * (b - a) - (a + b)) % 2 = 0

def SnowDepthFormula (a b : Int) (h_valid_input : ValidInput a b) (h_valid_snow : ValidSnowDepth a b (((b - a) * (b - a) - (a + b)) / 2)) : Int :=
  ((b - a) * (b - a) - (a + b)) / 2

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b ∧ ValidSnowDepth a b (((b - a) * (b - a) - (a + b)) / 2)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Extract the depth constraint from ValidSnowDepth
lemma snow_depth_positive (a b depth : Int) (h : ValidSnowDepth a b depth) : depth ≥ 1 :=
  h.1
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  SnowDepthFormula a b (h_precond.1) (h_precond.2)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result ≥ 1 ∧ result = SnowDepthFormula a b (h_precond.1) (h_precond.2)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- Prove result ≥ 1
    exact snow_depth_positive a b (((b - a) * (b - a) - (a + b)) / 2) h_precond.2
  · -- Prove result = SnowDepthFormula
    rfl
-- </vc-theorems>
