-- <vc-preamble>
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  result.fst = 2 * x ∧ result.snd = 2 * result.fst

theorem DoubleQuadruple_spec_satisfied (x: Int) (h_precond : DoubleQuadruple_precond (x)) :
    DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>