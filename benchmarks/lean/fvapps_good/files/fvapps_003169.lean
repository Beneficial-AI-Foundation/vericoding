-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reduce_fraction (p : Int × Int) : Int × Int := sorry

theorem reduce_fraction_result_is_int (p : Int × Int) (h : p.2 ≠ 0) : 
  ∃ (a b : Int), reduce_fraction p = (a, b) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reduce_fraction_denominator_positive (p : Int × Int) (h : p.2 ≠ 0) :
  (reduce_fraction p).2 > 0 := sorry

theorem reduce_fraction_preserves_value (p : Int × Int) (h : p.2 ≠ 0) :
  p.1 * (reduce_fraction p).2 = p.2 * (reduce_fraction p).1 := sorry 

theorem reduce_fraction_is_lowest_terms (p : Int × Int) (h : p.2 ≠ 0) :
  Nat.gcd ((Int.natAbs (reduce_fraction p).1)) (Int.natAbs (reduce_fraction p).2) = 1 := sorry

theorem reduce_fraction_zero (n : Int) (h : n ≠ 0) :
  reduce_fraction (0, n) = (0, 1) := sorry
-- </vc-theorems>