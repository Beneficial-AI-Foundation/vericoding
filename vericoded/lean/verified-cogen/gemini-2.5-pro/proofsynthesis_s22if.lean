import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Nat) :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- No helpers are needed, the proof is straightforward.
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond a sum N) : Array Int :=
  sum.set! 0 (3 * ↑N)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Nat) (result: Array Int) (h_precond : myfun_precond a sum N) :=
  result[0]! = 3 * N

theorem myfun_spec_satisfied (a: Array Int) (sum: Array Int) (N: Nat) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  simp [myfun, myfun_postcond, h_precond]
-- </vc-theorems>
