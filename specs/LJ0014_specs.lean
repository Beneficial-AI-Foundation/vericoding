-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (N : Nat) : Prop :=
  N > 0 ∧ a.size = N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (N : Nat) (h_precond : myfun_precond a N) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (N : Nat) (result: Array Int) (h_precond : myfun_precond a N) :=
  ∀ k : Int, 0 ≤ k ∧ k < N → result[k.toNat]! % 2 = N % 2

theorem myfun_spec_satisfied (a: Array Int) (N: Nat) (h_precond : myfun_precond a N) :
    myfun_postcond a N (myfun a N h_precond) h_precond := by
  sorry
-- </vc-theorems>