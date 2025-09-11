-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 10^9 + 7

def solve_prime_sum (n: Nat) : Nat :=
  sorry

/- Output is always within valid mod range -/
-- </vc-definitions>

-- <vc-theorems>
theorem solve_prime_sum_output_range (n: Nat) :
  solve_prime_sum n < MOD :=
  sorry

/- Function is deterministic for same input -/

theorem solve_prime_sum_deterministic (n: Nat) : 
  solve_prime_sum n = solve_prime_sum n :=
  sorry 

/- First values are monotonically increasing -/

theorem solve_prime_sum_monotone_init :
  solve_prime_sum 1 < solve_prime_sum 2 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_prime_sum 1

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_prime_sum 2

/-
info: 19
-/
-- #guard_msgs in
-- #eval solve_prime_sum 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded