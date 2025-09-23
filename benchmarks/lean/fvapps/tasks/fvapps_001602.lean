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
-- </vc-theorems>