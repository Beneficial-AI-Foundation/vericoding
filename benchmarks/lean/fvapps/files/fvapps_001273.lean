-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_valid_triangles (L K : Int) : Int := sorry

theorem count_valid_triangles_non_negative (L K : Int) :
  count_valid_triangles L K ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_valid_triangles_k_greater_l (L K : Int) :
  K > L → count_valid_triangles L K = 0 := sorry

theorem count_valid_triangles_k_one (L : Int) :
  L ≥ 1 → count_valid_triangles L 1 = (L * (L + 1)) / 2 := sorry

theorem count_valid_triangles_k_equals_l (L : Int) :
  L ≥ 1 → count_valid_triangles L L = 1 := sorry

theorem count_valid_triangles_monotonic (L k1 k2 : Int) :
  L ≥ 1 → k1 ≤ k2 → k2 ≤ L →
  count_valid_triangles L k1 ≥ count_valid_triangles L k2 := sorry
-- </vc-theorems>