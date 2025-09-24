-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>