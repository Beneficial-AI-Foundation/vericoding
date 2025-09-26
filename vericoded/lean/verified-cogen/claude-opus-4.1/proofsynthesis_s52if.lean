import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Nat) : Prop :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond a sum N) : Array Int :=
  let result : Array Int := Array.mk [Int.ofNat (6 * N)]
  result
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Nat) (result : Array Int) (h_precond : myfun_precond a sum N) : Prop :=
  result[0]! = 6 * N

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  unfold myfun_postcond myfun
  simp only [Array.getElem!_eq_getD]
  rfl
-- </vc-theorems>

def main : IO Unit := do
  return ()