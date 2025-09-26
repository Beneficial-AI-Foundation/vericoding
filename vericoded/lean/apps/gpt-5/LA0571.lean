import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length = 4 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.get (String.Pos.mk i) = '+' ∨ s.get (String.Pos.mk i) = '-'

def CountChar (s : String) (c : Char) : Int :=
  s.toList.filter (· = c) |>.length

def CalculateSum (s : String) : Int :=
  CountChar s '+' - CountChar s '-'

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma CalculateSum_def (s : String) :
  CalculateSum s = CountChar s '+' - CountChar s '-' := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  CalculateSum s
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result: Int) (h_precond : solve_precond s) : Prop :=
  result = CalculateSum s

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
