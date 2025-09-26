import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (b : Array Int) (c : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N.natAbs ∧ b.size = N.natAbs ∧ c.size = N.natAbs ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (b : Array Int) (c : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b c sum N) : Array Int :=
  Array.replicate 1 (3 * N)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (b : Array Int) (c : Array Int) (sum : Array Int) (N : Int) (result : Array Int) (h_precond : myfun_precond a b c sum N) :=
  result[0]! ≤ 3 * N

theorem myfun_spec_satisfied (a : Array Int) (b : Array Int) (c : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b c sum N) :
    myfun_postcond a b c sum N (myfun a b c sum N h_precond) h_precond := by
  simp [myfun, myfun_postcond]
-- </vc-theorems>
