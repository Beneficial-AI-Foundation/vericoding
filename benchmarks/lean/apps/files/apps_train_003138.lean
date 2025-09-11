-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def evenFib (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem evenFib_nonnegative (n : Int) : evenFib n ≥ 0 :=
  sorry

theorem evenFib_nonpositive_input (n : Int) (h : n ≤ 0) : evenFib n = 0 :=
  sorry

theorem evenFib_monotonic (n : Int) (h : n > 0) : evenFib n ≥ evenFib (n-1) :=
  sorry

theorem evenFib_even (n : Int) (h : n > 0) : evenFib n % 2 = 0 :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval even_fib 10

/-
info: 0
-/
-- #guard_msgs in
-- #eval even_fib 0

/-
info: 44
-/
-- #guard_msgs in
-- #eval even_fib 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded