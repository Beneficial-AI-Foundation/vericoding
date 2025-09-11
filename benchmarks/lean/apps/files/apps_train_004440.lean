-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_fib (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_fib_nonnegative (n: Nat) (h: n > 0) : sum_fib n ≥ 0 :=
  sorry

theorem sum_fib_base_case_1 : sum_fib 1 = 1 :=
  sorry

theorem sum_fib_base_case_2 : sum_fib 2 = 2 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval sum_fib 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval sum_fib 3

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_fib 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible