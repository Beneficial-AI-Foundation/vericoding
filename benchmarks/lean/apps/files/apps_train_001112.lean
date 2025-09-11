-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_squares (n : Nat) : Nat := sorry

/- Every positive number can be decomposed into a sum of squares,
    and the count of squares is positive and not larger than the input number -/
-- </vc-definitions>

-- <vc-theorems>
theorem count_squares_basic_properties (n : Nat) (h : n > 0) :
  let result := count_squares n
  0 < result ∧ result ≤ n := sorry

/- The decomposition count equals 1 for perfect squares -/

theorem count_squares_perfect (n : Nat) (h : n > 0) :
  count_squares (n * n) = 1 := sorry

/- Basic results for small numbers -/

theorem count_squares_small_numbers :
  count_squares 1 = 1 ∧ 
  count_squares 2 = 2 ∧ 
  count_squares 3 = 3 := sorry

/- The sum of squares used in decomposition equals the input number -/

theorem count_squares_sum_property (n : Nat) (h : n > 0) :
  ∃ (squares : List Nat),
    squares.length ≤ count_squares n ∧
    (∀ x ∈ squares, ∃ k, x = k * k) ∧
    (squares.foldl (· + ·) 0 = n) := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_squares 85

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_squares 114

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_squares 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded