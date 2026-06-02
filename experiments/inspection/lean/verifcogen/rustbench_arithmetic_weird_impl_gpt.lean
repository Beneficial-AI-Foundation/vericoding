import Mathlib
-- <vc-preamble>
@[reducible, simp]
def arithmeticWeird_precond : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma int_zero_lt_ten : (0 : Int) < 10 := by decide
-- </vc-helpers>

-- <vc-definitions>
def arithmeticWeird (h_precond : arithmeticWeird_precond) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arithmeticWeird_postcond (result: Int) (h_precond : arithmeticWeird_precond) :=
  result < 10

theorem arithmeticWeird_spec_satisfied (h_precond : arithmeticWeird_precond) :
    arithmeticWeird_postcond (arithmeticWeird h_precond) h_precond := by
  simpa [arithmeticWeird, arithmeticWeird_postcond] using int_zero_lt_ten
-- </vc-theorems>
