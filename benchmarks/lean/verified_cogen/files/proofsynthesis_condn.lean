-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (N : Int) (m : Int) :=
  N > 0 ∧ a.size = N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (N : Int) (m : Int) (h_precond : myfun_precond a N m) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (N : Int) (m : Int) (result: Array Int) (h_precond : myfun_precond a N m) :=
  ∀ k : Int, 0 ≤ k ∧ k < N → result[k.toNat]! ≤ N

theorem myfun_spec_satisfied (a: Array Int) (N: Int) (m: Int) (h_precond : myfun_precond a N m) :
    myfun_postcond a N m (myfun a N m h_precond) h_precond := by
  sorry
-- </vc-theorems>