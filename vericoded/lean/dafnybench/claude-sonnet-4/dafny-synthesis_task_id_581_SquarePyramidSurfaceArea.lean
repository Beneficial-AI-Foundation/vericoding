import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Integer arithmetic lemmas
lemma int_mul_assoc (a b c : Int) : a * (b * c) = (a * b) * c := (mul_assoc a b c).symm
lemma int_mul_comm (a b : Int) : a * b = b * a := mul_comm a b
lemma int_add_mul_distrib (a b c : Int) : (a + b) * c = a * c + b * c := add_mul a b c
lemma int_mul_add_distrib (a b c : Int) : a * (b + c) = a * b + a * c := mul_add a b c
-- </vc-helpers>

-- <vc-definitions>
def SquarePyramidSurfaceArea (baseEdge : Int) (height : Int) : Int :=
baseEdge * baseEdge + 2 * baseEdge * height
-- </vc-definitions>

-- <vc-theorems>
theorem SquarePyramidSurfaceArea_spec (baseEdge height : Int) :
baseEdge > 0 →
height > 0 →
SquarePyramidSurfaceArea baseEdge height = baseEdge * baseEdge + 2 * baseEdge * height :=
by
  intros h1 h2
  unfold SquarePyramidSurfaceArea
  rfl
-- </vc-theorems>
