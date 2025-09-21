-- <vc-preamble>
@[reducible, simp]
def arithmeticWeird_precond : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arithmeticWeird (h_precond : arithmeticWeird_precond) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arithmeticWeird_postcond (result: Int) (h_precond : arithmeticWeird_precond) :=
  result < 10

theorem arithmeticWeird_spec_satisfied (h_precond : arithmeticWeird_precond) :
    arithmeticWeird_postcond (arithmeticWeird h_precond) h_precond := by
  sorry
-- </vc-theorems>