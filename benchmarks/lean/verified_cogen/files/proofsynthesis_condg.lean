-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) : Prop :=
  N > 0 ∧ a.size = N.natAbs ∧ sum.size = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result : Array Int × Array Int) (h_precond : myfun_precond a sum N) : Prop :=
  ∀ k : Int, 0 ≤ k ∧ k < N → result.1[k.natAbs]! = 0

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  sorry
-- </vc-theorems>