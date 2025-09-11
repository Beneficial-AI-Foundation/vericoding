-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factor_sum (n : Nat) : Nat := sorry 

def sum_of_prime_factors (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem factor_sum_positive {n : Nat} (h : n ≥ 2) :
  factor_sum n > 0 := sorry

theorem factor_sum_idempotent {n : Nat} (h : n ≥ 2) :
  factor_sum (factor_sum n) = factor_sum n := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval factor_sum 24

/-
info: 7
-/
-- #guard_msgs in
-- #eval factor_sum 35

/-
info: 5
-/
-- #guard_msgs in
-- #eval factor_sum 156
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible