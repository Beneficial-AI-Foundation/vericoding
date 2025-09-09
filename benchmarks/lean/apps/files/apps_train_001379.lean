-- <vc-helpers>
-- </vc-helpers>

def min_candies_required (n k : Nat) : Nat :=
  sorry

theorem min_candies_at_least_n (n k : Nat) (h1: n > 0) (h2: k ≤ 1000) : 
  min_candies_required n k ≥ n :=
sorry

theorem min_candies_at_least_half_times_k (n k : Nat) (h1: n > 0) (h2: k ≤ 1000) :
  min_candies_required n k ≥ (n/2) * k :=
sorry

theorem min_candies_increases_with_k (n k : Nat) (h1: n > 1) (h2: k > 0) (h3: k ≤ 1000) :
  min_candies_required n k > min_candies_required n (k-1) :=
sorry

theorem min_candies_increases_with_n (n k : Nat) (h1: n > 1) (h2: k ≤ 1000) :
  min_candies_required n k ≥ min_candies_required (n-1) k :=
sorry

theorem min_candies_zero_diff (n : Nat) (h: n > 0) :
  min_candies_required n 0 = n :=
sorry

theorem min_candies_odd_greater (n k : Nat) (h1: n > 1) (h2: n % 2 = 1) (h3: k ≤ 1000) :
  min_candies_required n k > min_candies_required (n-1) k :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_candies_required 2 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_candies_required 3 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_candies_required 4 0

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible