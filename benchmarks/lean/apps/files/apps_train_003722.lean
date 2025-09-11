-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hamming_distance : Int → Int → Nat := 
  sorry

/- Hamming distance is symmetric -/
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_distance_symmetric (a b : Int) : 
  hamming_distance a b = hamming_distance b a := by
  sorry

/- Hamming distance between a number and itself is zero -/

theorem hamming_distance_self_zero (a : Int) : 
  hamming_distance a a = 0 := by
  sorry

/- Hamming distance satisfies the triangle inequality -/

theorem hamming_distance_triangle_inequality (a b c : Int) :
  hamming_distance a c ≤ hamming_distance a b + hamming_distance b c := by
  sorry

/- Hamming distance is always nonnegative -/

theorem hamming_distance_nonnegative (a b : Int) :
  hamming_distance a b ≥ 0 := by
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance 25 87

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance 256 302

/-
info: 4
-/
-- #guard_msgs in
-- #eval hamming_distance 543 634
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded