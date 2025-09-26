-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_zeros (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_zeros_nonnegative (s: String) :
  count_zeros s ≥ 0 := sorry

theorem count_zeros_upper_bound (s: String) :
  count_zeros s ≤ 2 * s.length := sorry

theorem count_zeros_concatenation (s: String) :
  count_zeros (s ++ s) = count_zeros s * 2 := sorry

theorem count_zeros_case_insensitive (c: Char) :
  c ∈ ['d', 'o', 'p', 'q'] →
  count_zeros (String.mk [c]) = count_zeros (String.mk [c.toUpper]) := sorry

theorem count_zeros_parentheses :
  count_zeros "()" = 1 := sorry
-- </vc-theorems>