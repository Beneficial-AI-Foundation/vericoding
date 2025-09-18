-- <vc-preamble>
def MOD := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_crowds (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_crowds_nonnegative (n : Nat) :
  solve_crowds n ≥ 0 ∧ solve_crowds n < MOD :=
sorry

theorem solve_crowds_small_n (n : Nat) (h : n ≤ 2) :
  solve_crowds n = 0 :=
sorry

theorem solve_crowds_upper_bound (n : Nat) (h : n ≥ 3) :
  solve_crowds n < 2^n :=
sorry

theorem solve_crowds_known_values_3 :
  solve_crowds 3 = 1 :=
sorry

theorem solve_crowds_known_values_4 :
  solve_crowds 4 = 3 :=
sorry
-- </vc-theorems>