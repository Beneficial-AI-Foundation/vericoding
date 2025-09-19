-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hamming_distance : Int → Int → Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_distance_symmetric (a b : Int) :
  hamming_distance a b = hamming_distance b a := by
  sorry

theorem hamming_distance_self_zero (a : Int) :
  hamming_distance a a = 0 := by
  sorry

theorem hamming_distance_triangle_inequality (a b c : Int) :
  hamming_distance a c ≤ hamming_distance a b + hamming_distance b c := by
  sorry

theorem hamming_distance_nonnegative (a b : Int) :
  hamming_distance a b ≥ 0 := by
  sorry
-- </vc-theorems>