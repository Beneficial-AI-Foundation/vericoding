-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def halving_sum (n : Nat) : Nat := sorry

/- For any positive n, halving_sum(n) is at least n -/
-- </vc-definitions>

-- <vc-theorems>
theorem halving_sum_lower_bound (n : Nat) (h : n > 0) : 
  halving_sum n ≥ n := sorry

/- For any positive n, halving_sum(n) is less than 2*n -/

theorem halving_sum_upper_bound (n : Nat) (h : n > 0) :
  halving_sum n < 2*n := sorry

/- For powers of 2, halving_sum(n) equals 2*n - 1 -/

theorem halving_sum_power_of_two (n : Nat) (h : n > 0) 
  (h_pow : ∃ k, n = 2^k) :
  halving_sum n = 2*n - 1 := sorry

/- Base cases for n=1 and n=2 -/

theorem halving_sum_base_cases :
  (halving_sum 1 = 1) ∧ (halving_sum 2 = 3) := sorry

/-
info: 47
-/
-- #guard_msgs in
-- #eval halving_sum 25

/-
info: 247
-/
-- #guard_msgs in
-- #eval halving_sum 127

/-
info: 1
-/
-- #guard_msgs in
-- #eval halving_sum 1
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded