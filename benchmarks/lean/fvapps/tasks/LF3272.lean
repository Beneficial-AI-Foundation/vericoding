-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_perfect_square (n: Int) : Int := sorry

theorem next_perfect_square_non_negative (n: Int) : 
  next_perfect_square n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_perfect_square_negative_input (n: Int) : 
  n < 0 → next_perfect_square n = 0 := sorry

theorem next_perfect_square_is_perfect (n: Int) (h: n ≥ 0) :
  ∃ m: Int, next_perfect_square n = m * m := sorry

theorem next_perfect_square_greater_than_input (n: Int) (h: n ≥ 0) :
  next_perfect_square n > n := sorry

theorem next_perfect_square_is_smallest (n: Int) (h: n ≥ 0) :
  ∀ m: Int, m * m > next_perfect_square n → m * m > n := sorry

theorem next_perfect_square_of_perfect_square (n: Int) (h: n ≥ 0) :
  next_perfect_square (n * n) = (n + 1) * (n + 1) := sorry
-- </vc-theorems>