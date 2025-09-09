-- <vc-helpers>
-- </vc-helpers>

def count_ways_to_climb (n : Nat) : Nat :=
  sorry

theorem count_ways_positive (n : Nat) (h : n > 0) :
  count_ways_to_climb n > 0 :=
sorry

theorem count_ways_upper_bound (n : Nat) (h : n > 0) :
  count_ways_to_climb n ≤ n :=
sorry

theorem count_ways_lower_bound (n : Nat) (h : n > 0) :
  count_ways_to_climb n ≥ (n + 1) / 2 :=
sorry

theorem count_ways_base_cases :
  count_ways_to_climb 1 = 1 ∧ count_ways_to_climb 2 = 2 :=
sorry

theorem count_ways_even (n : Nat) (h₁ : n > 0) (h₂ : n % 2 = 0) :
  count_ways_to_climb n = n/2 + 1 :=
sorry

theorem count_ways_odd (n : Nat) (h₁ : n > 0) (h₂ : n % 2 = 1) :
  count_ways_to_climb n = (n-1)/2 + 1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_ways_to_climb 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_ways_to_climb 4

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_ways_to_climb 5

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible