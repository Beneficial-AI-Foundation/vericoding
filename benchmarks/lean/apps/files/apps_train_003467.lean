-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divisible_count (x : Nat) (y : Nat) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisible_count_zero_width (x k : Nat) (h : k > 0) :
  divisible_count x (x-1) k = 0 :=
  sorry

theorem divisible_count_step (x y k : Nat) (h : k > 0) (h2 : (y + 1) % k = 0) :
  divisible_count x (y + k) k = divisible_count x y k + 1 :=
  sorry

theorem divisible_count_periodic (x k : Nat) (h : k > 0) :
  divisible_count x (x + k - 1) k = divisible_count (x + k) (x + 2*k - 1) k :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval divisible_count 6 11 2

/-
info: 20
-/
-- #guard_msgs in
-- #eval divisible_count 11 345 17

/-
info: 1
-/
-- #guard_msgs in
-- #eval divisible_count 0 1 7
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible