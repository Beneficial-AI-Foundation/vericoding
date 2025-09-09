-- <vc-helpers>
-- </vc-helpers>

def fusc (n : Nat) : Nat := sorry

theorem fusc_non_negative (n : Nat) : fusc n ≥ 0 := sorry

theorem fusc_even_reduce (n : Nat) (h : n > 0) (h2 : n % 2 = 0) : 
  fusc n = fusc (n / 2) := sorry

theorem fusc_odd_sum (n : Nat) (h : n % 2 = 1) :
  fusc n = fusc (n / 2) + fusc (n / 2 + 1) := sorry

theorem fusc_base_cases :
  fusc 0 = 0 ∧ fusc 1 = 1 := sorry

theorem fusc_monotonic_bound (n : Nat) :
  fusc n ≤ n := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval fusc 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval fusc 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval fusc 10

-- Apps difficulty: introductory
-- Assurance level: unguarded