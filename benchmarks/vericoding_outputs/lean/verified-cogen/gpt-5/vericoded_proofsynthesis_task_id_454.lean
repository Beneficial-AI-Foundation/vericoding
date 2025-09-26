import Mathlib
-- <vc-preamble>
@[reducible, simp]
def containsZ_precond (text : Array Char) :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
noncomputable instance instCoePropBoolDecide : Coe Prop Bool where
  coe p := by
    classical
    exact decide p
-- </vc-helpers>

-- <vc-definitions>
def containsZ (text : Array Char) (h_precond : containsZ_precond (text)) : Bool :=
  by
  classical
  exact decide (∃ i, i < text.size ∧ (text[i]! = 'Z' ∨ text[i]! = 'z'))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsZ_postcond (text : Array Char) (result: Bool) (h_precond : containsZ_precond (text)) :=
  result = (∃ i, i < text.size ∧ (text[i]! = 'Z' ∨ text[i]! = 'z'))

theorem containsZ_spec_satisfied (text: Array Char) (h_precond : containsZ_precond (text)) :
    containsZ_postcond (text) (containsZ (text) h_precond) h_precond := by
  rfl
-- </vc-theorems>
