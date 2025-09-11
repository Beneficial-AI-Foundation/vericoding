-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_fib (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fib_sum_of_previous (n : Nat) (h : n ≥ 3) : 
  nth_fib n = nth_fib (n-1) + nth_fib (n-2) :=
  sorry

theorem fib_nonnegative (n : Nat) (h : n > 0) :
  nth_fib n ≥ 0 :=
  sorry

theorem fib_first_two : 
  nth_fib 1 = 0 ∧ nth_fib 2 = 1 :=
  sorry

theorem fib_strictly_increasing (n : Nat) (h : n ≥ 4) :
  nth_fib n > nth_fib (n-1) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval nth_fib 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_fib 4

/-
info: 34
-/
-- #guard_msgs in
-- #eval nth_fib 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible