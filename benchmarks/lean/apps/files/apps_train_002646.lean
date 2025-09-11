-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fib_rabbits (n : Nat) (b : Nat) : Nat := sorry

theorem fib_rabbits_nonnegative (n : Nat) (b : Nat) (h : b > 0) :
  fib_rabbits n b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fib_rabbits_monotone (n : Nat) (b : Nat) (h1 : b > 0) (h2 : n > 2) :
  fib_rabbits n b ≥ fib_rabbits (n-1) b := sorry

theorem fib_rabbits_bound (n : Nat) (b : Nat) (h1 : b > 0) (h2 : n > 1) :
  fib_rabbits n b ≤ fib_rabbits (n-1) b * b + fib_rabbits (n-2) b := sorry 

theorem fib_rabbits_zero (b : Nat) (h : b > 0) :
  fib_rabbits 0 b = 0 := sorry

/-
info: 19
-/
-- #guard_msgs in
-- #eval fib_rabbits 5 3

/-
info: 40
-/
-- #guard_msgs in
-- #eval fib_rabbits 6 3

/-
info: 201
-/
-- #guard_msgs in
-- #eval fib_rabbits 4 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible