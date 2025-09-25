-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_squares (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_squares_basic_properties (n : Nat) (h : n > 0) :
  let result := count_squares n
  0 < result ∧ result ≤ n :=
sorry

theorem count_squares_perfect (n : Nat) (h : n > 0) :
  count_squares (n * n) = 1 :=
sorry

theorem count_squares_small_numbers :
  count_squares 1 = 1 ∧
  count_squares 2 = 2 ∧
  count_squares 3 = 3 :=
sorry

theorem count_squares_sum_property (n : Nat) (h : n > 0) :
  ∃ (squares : List Nat),
    squares.length ≤ count_squares n ∧
    (∀ x ∈ squares, ∃ k, x = k * k) ∧
    (squares.foldl (· + ·) 0 = n) :=
sorry
-- </vc-theorems>