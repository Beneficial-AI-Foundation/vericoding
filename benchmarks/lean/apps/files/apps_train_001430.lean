-- <vc-helpers>
-- </vc-helpers>

def calc_robbery_probability (n : Nat) : Nat × Nat := sorry

-- Basic properties

theorem robbery_prob_numerator (n : Nat) (h : n > 0) : 
  (calc_robbery_probability n).1 = 1 := sorry 

theorem robbery_prob_denominator (n : Nat) (h : n > 0) :
  (calc_robbery_probability n).2 = 10 ^ (n / 2) := sorry

theorem robbery_prob_consistent (n : Nat) (h : n > 0) :
  calc_robbery_probability n = calc_robbery_probability n := sorry

-- Monotonicity property

theorem robbery_prob_monotonic (n : Nat) (h : n > 1) :
  (calc_robbery_probability (n-1)).2 ≤ (calc_robbery_probability n).2 := sorry

/-
info: (1, 1)
-/
-- #guard_msgs in
-- #eval calc_robbery_probability 1

/-
info: (1, 10)
-/
-- #guard_msgs in
-- #eval calc_robbery_probability 2

/-
info: (1, 10)
-/
-- #guard_msgs in
-- #eval calc_robbery_probability 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible