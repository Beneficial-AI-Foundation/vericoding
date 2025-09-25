-- <vc-preamble>
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Compare_postcond (a : Int) (b : Int) (result: Bool) (h_precond : Compare_precond (a) (b)) :=
  (a = b → result = true) ∧ (a ≠ b → result = false)

theorem Compare_spec_satisfied (a: Int) (b: Int) (h_precond : Compare_precond (a) (b)) :
    Compare_postcond (a) (b) (Compare (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>