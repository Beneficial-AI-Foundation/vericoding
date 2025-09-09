def log10 (n : Nat) : Nat :=
  if n < 10 then 0
  else 1 + log10 (n / 10)

-- <vc-helpers>
-- </vc-helpers>

def rocks (n : Nat) : Nat := sorry

theorem rocks_monotonically_increasing 
  (n : Nat)
  (h : n > 1) :
  rocks n ≥ rocks (n-1) := sorry

theorem rocks_minimum_bound
  (n : Nat)
  (h : n > 0) : 
  rocks n ≥ n := sorry

theorem rocks_single_digit 
  (n : Nat)
  (h1 : n > 0)
  (h2 : n ≤ 9) :
  rocks n = n := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval rocks 1

/-
info: 17
-/
-- #guard_msgs in
-- #eval rocks 13

/-
info: 192
-/
-- #guard_msgs in
-- #eval rocks 100

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible