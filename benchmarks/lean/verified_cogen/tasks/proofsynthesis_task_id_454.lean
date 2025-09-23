-- <vc-preamble>
@[reducible, simp]
def containsZ_precond (text : Array Char) :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsZ (text : Array Char) (h_precond : containsZ_precond (text)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsZ_postcond (text : Array Char) (result: Bool) (h_precond : containsZ_precond (text)) :=
  result = (∃ i, i < text.size ∧ (text[i]! = 'Z' ∨ text[i]! = 'z'))

theorem containsZ_spec_satisfied (text: Array Char) (h_precond : containsZ_precond (text)) :
    containsZ_postcond (text) (containsZ (text) h_precond) h_precond := by
  sorry
-- </vc-theorems>