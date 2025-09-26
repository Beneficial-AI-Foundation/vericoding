import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Nat) :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond (a) (sum) (N)) : Array Int :=
  Array.singleton (5 * N : Int)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Nat) (result: Array Int) (h_precond : myfun_precond (a) (sum) (N)) :=
  result[0]! = 5 * N

theorem myfun_spec_satisfied (a: Array Int) (sum: Array Int) (N: Nat) (h_precond : myfun_precond (a) (sum) (N)) :
    myfun_postcond (a) (sum) (N) (myfun (a) (sum) (N) h_precond) h_precond := by
  unfold myfun myfun_postcond
  simp [Array.singleton]
-- </vc-theorems>

def main : IO Unit := do
  pure ()