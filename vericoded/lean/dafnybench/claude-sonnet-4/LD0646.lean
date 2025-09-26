import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- Helper functions and lemmas for triangular prism volume calculations
-- No additional helpers needed for this implementation
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
  intros h_base h_height h_length
  rfl
-- </vc-theorems>
