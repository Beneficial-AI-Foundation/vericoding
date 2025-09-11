-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_even (n : Nat) : Nat := sorry

theorem nth_even_increases_monotonically {n : Nat} (h : n > 0) : 
  nth_even (n + 1) > nth_even n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nth_even_is_even {n : Nat} (h : n > 0) :
  nth_even n % 2 = 0 := sorry

theorem nth_even_formula {n : Nat} (h : n > 0) :
  nth_even n = 2 * (n - 1) := sorry

theorem nth_even_reverses_with_division {n : Nat} (h1 : n > 0) (h2 : n ≤ 10000) :
  (nth_even n) / 2 + 1 = n := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval nth_even 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_even 2

/-
info: 198
-/
-- #guard_msgs in
-- #eval nth_even 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible