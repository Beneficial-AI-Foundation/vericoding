-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_number (n : Nat) (x : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_number_non_negative (n : Nat) (x : Nat) (h : n > 0) :
  count_number n x ≥ 0 :=
sorry

theorem count_number_upper_bound (n : Nat) (x : Nat) (h : n > 0) : 
  count_number n x ≤ n :=
sorry

theorem count_number_above_max (n : Nat) (h : n > 0) :
  count_number n (n*n + 1) = 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_number 5 5

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_number 10 5

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_number 6 12
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible