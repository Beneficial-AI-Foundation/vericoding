-- <vc-preamble>
-- Precondition function for myfun2
@[reducible, simp]
def myfun2_precond (x : Array Int) : Prop :=
  ∀ k, 0 ≤ k ∧ k < x.size → x[k]! ≤ 0x7FFFBFFB
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun2 (x : Array Int) (h_precond : myfun2_precond x) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun2_postcond (x_old : Array Int) (x_new : Array Int) (h_precond : myfun2_precond x_old) : Prop :=
  x_new.size = x_old.size ∧ 
  (∀ k, 0 ≤ k ∧ k < x_new.size → x_new[k]! = x_old[k]! + 4)

theorem myfun2_spec_satisfied (x : Array Int) (h_precond : myfun2_precond x) :
    myfun2_postcond x (myfun2 x h_precond) h_precond := by
  sorry
-- </vc-theorems>