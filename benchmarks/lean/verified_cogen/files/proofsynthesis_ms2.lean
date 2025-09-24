-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Nat) (sum : Array Nat) (N : Nat) :=
  a.size = N ∧ sum.size = 1 ∧ N > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Nat) (sum : Array Nat) (N : Nat) (h_precond : myfun_precond a sum N) : Array Nat × Array Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Nat) (sum : Array Nat) (N : Nat) (result_a : Array Nat) (result_sum : Array Nat) (h_precond : myfun_precond a sum N) :=
  result_sum[0]! ≤ N

theorem myfun_spec_satisfied (a : Array Nat) (sum : Array Nat) (N : Nat) (h_precond : myfun_precond a sum N) :
    let (result_a, result_sum) := myfun a sum N h_precond
    myfun_postcond a sum N result_a result_sum h_precond := by
  sorry
-- </vc-theorems>