-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) : Prop :=
  N > 0 ∧ a.size = N.natAbs ∧ b.size = N.natAbs ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b sum N) : Array Int × Array Int × Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a_old : Array Int) (b_old : Array Int) (sum_old : Array Int) (N : Int) (result : Array Int × Array Int × Array Int) (h_precond : myfun_precond a_old b_old sum_old N) : Prop :=
  ∀ k : Int, 0 ≤ k ∧ k < N → result.1[k.natAbs]! = 2 * N + 1

theorem myfun_spec_satisfied (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b sum N) :
    myfun_postcond a b sum N (myfun a b sum N h_precond) h_precond := by
  sorry
-- </vc-theorems>