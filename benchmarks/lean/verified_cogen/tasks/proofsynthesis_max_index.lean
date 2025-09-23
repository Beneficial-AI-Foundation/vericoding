-- <vc-preamble>
@[reducible, simp]
def myfun1_precond (x : Array Int) : Prop :=
  x.size ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun1 (x : Array Int) (h_precond : myfun1_precond x) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun1_postcond (x : Array Int) (max_index : Nat) (h_precond : myfun1_precond x) : Prop :=
  (∀ k, k < x.size → x[max_index]! ≥ x[k]!) ∧ max_index < x.size

theorem myfun1_spec_satisfied (x : Array Int) (h_precond : myfun1_precond x) :
    myfun1_postcond x (myfun1 x h_precond) h_precond := by
  sorry
-- </vc-theorems>