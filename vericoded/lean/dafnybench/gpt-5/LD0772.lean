import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VeriCoding

/-- A harmless helper alias for squaring an integer. -/
abbrev square (z : Int) : Int := z * z

@[simp] lemma square_def (z : Int) : square z = z * z := rfl

end VeriCoding

-- </vc-helpers>

-- <vc-definitions>
def AreaOfLargestTriangleInSemicircle (radius : Int) : Int :=
radius * radius
-- </vc-definitions>

-- <vc-theorems>
theorem AreaOfLargestTriangleInSemicircle_spec (radius : Int) :
radius > 0 →
AreaOfLargestTriangleInSemicircle radius = radius * radius :=
by
  intro _
  rfl
-- </vc-theorems>
