-- <vc-preamble>
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def MultipleReturns_postcond (x : Int) (y : Int) (result: (Int × Int)) (h_precond : MultipleReturns_precond (x) (y)) :=
  result.1 = x + y ∧ result.2 + y = x

theorem MultipleReturns_spec_satisfied (x: Int) (y: Int) (h_precond : MultipleReturns_precond (x) (y)) :
    MultipleReturns_postcond (x) (y) (MultipleReturns (x) (y) h_precond) h_precond := by
  sorry
-- </vc-theorems>