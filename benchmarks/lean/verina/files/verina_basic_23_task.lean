-- <vc-preamble>
@[reducible, simp]
def differenceMinMax_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def differenceMinMax_postcond (a : Array Int) (result: Int) (h_precond : differenceMinMax_precond (a)) :=
  result + (a.foldl (fun acc x => if x < acc then x else acc) (a[0]!)) = (a.foldl (fun acc x => if x > acc then x else acc) (a[0]!))

theorem differenceMinMax_spec_satisfied (a: Array Int) (h_precond : differenceMinMax_precond (a)) :
    differenceMinMax_postcond (a) (differenceMinMax (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>