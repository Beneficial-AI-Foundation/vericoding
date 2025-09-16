-- <vc-preamble>
def doors (n : Nat) : Nat := sorry

theorem doors_non_negative (n : Nat) : 
  doors n ≥ 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry

theorem doors_squared_leq (n : Nat) :
  (doors n) * (doors n) ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem doors_plus_one_squared_gt (n : Nat) :
  (doors n + 1) * (doors n + 1) > n := sorry

theorem doors_perfect_squares (n : Nat) :
  doors (n * n) = n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval doors 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval doors 10

/-
info: 10
-/
-- #guard_msgs in
-- #eval doors 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible