-- <vc-preamble>
@[reducible, simp]
def abs_precond (x : Int) : Prop :=
  x ≠ Int.negSucc 2147483647
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) (h_precond : abs_precond x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def abs_postcond (x : Int) (result : Int) (h_precond : abs_precond x) : Prop :=
  result ≥ 0 ∧ (result = x ∨ result = -x)

theorem abs_spec_satisfied (x : Int) (h_precond : abs_precond x) :
    abs_postcond x (abs x h_precond) h_precond := by
  sorry
-- </vc-theorems>