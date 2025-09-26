import Mathlib
-- <vc-preamble>
-- Precondition definitions
@[reducible, simp]
def myfun_precond (a : Array Nat) (sum : Array Nat) (N : Nat) : Prop :=
  a.size = N ∧ sum.size = 1 ∧ N > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma get_zero_singleton_nat : (#[0] : Array Nat)[0]! = 0 := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Nat) (sum : Array Nat) (N : Nat) (h_precond : myfun_precond a sum N) : Array Nat × Array Nat :=
  (a, #[0])
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Nat) (sum : Array Nat) (N : Nat) (result : Array Nat × Array Nat) (h_precond : myfun_precond a sum N) : Prop :=
  result.2[0]! = 0

theorem myfun_spec_satisfied (a : Array Nat) (sum : Array Nat) (N : Nat) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  simp [myfun_postcond, myfun]
-- </vc-theorems>
