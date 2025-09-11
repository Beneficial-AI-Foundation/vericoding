-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countDivisors (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_divisors_monotonic
  {n : Nat}
  (h : n > 0)
  (h' : n ≤ 1000) :
  countDivisors (n + 1) ≥ countDivisors n :=
sorry

theorem count_divisors_positive
  {n : Nat}
  (h : n > 0)
  (h' : n ≤ 1000) :
  countDivisors n > 0 ∧ countDivisors n ≥ n :=
sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_divisors 5

/-
info: 27
-/
-- #guard_msgs in
-- #eval count_divisors 10

/-
info: 66
-/
-- #guard_msgs in
-- #eval count_divisors 20
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded