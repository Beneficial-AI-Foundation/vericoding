-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_squares (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_squares_monotonic (n : Nat) (h : n > 0) :
  count_squares (n + 1) > count_squares n :=
  sorry

theorem count_squares_positive (n : Nat) (h : n > 0) :
  count_squares n > 0 :=
  sorry

theorem count_squares_base_cases :
  count_squares 1 = 1 ∧ count_squares 2 = 5 :=
  sorry

theorem count_squares_min_bound (n : Nat) (h : n > 0) :
  count_squares n ≥ n * n :=
  sorry
-- </vc-theorems>