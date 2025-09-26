import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma mul_assoc_int (a b c : Int) : (a * b) * c = a * (b * c) := by
  simpa [mul_assoc]

-- </vc-helpers>

-- <vc-definitions>
def TriangularPrismVolume (base : Int) (height : Int) (length : Int) : Int :=
(base * height * length) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem TriangularPrismVolume_spec (base height length : Int) :
base > 0 →
height > 0 →
length > 0 →
TriangularPrismVolume base height length = (base * height * length) / 2 :=
by
  intro hb hh hl
  rfl
-- </vc-theorems>
