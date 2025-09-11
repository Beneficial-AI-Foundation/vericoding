-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_squareable (n : Nat) : Nat := sorry

theorem count_squareable_positive (n : Nat) (h : n > 0) : count_squareable n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_squareable_upper_bound (n : Nat) : count_squareable n ≤ n := sorry

theorem count_squareable_formula (n : Nat) : count_squareable n = n/4 + (n+1)/2 := sorry

theorem count_squareable_monotonic (n : Nat) (h : n > 1) : 
  count_squareable (n-1) ≤ count_squareable n := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_squareable 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_squareable 5

/-
info: 7
-/
-- #guard_msgs in
-- #eval count_squareable 10

/-
info: 15
-/
-- #guard_msgs in
-- #eval count_squareable 20

/-
info: 4820
-/
-- #guard_msgs in
-- #eval count_squareable 6427
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible