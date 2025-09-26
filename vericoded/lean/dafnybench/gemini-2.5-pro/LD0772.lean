import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- 
A helper lemma to show that integer division by 2 cancels multiplication by 2.
This is a specific case of `Int.mul_ediv_cancel_left`.
-/
lemma div2_mul_cancel (n : Int) : (2 * n) / 2 = n := by
  apply Int.mul_ediv_cancel_left
  norm_num

-- </vc-helpers>

-- <vc-definitions>
def AreaOfLargestTriangleInSemicircle (radius : Int) : Int :=
(2 * radius * radius) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem AreaOfLargestTriangleInSemicircle_spec (radius : Int) :
radius > 0 →
AreaOfLargestTriangleInSemicircle radius = radius * radius :=
by
  intro h_radius_pos
  dsimp [AreaOfLargestTriangleInSemicircle]
  rw [mul_assoc]
  rw [div2_mul_cancel]
-- </vc-theorems>
