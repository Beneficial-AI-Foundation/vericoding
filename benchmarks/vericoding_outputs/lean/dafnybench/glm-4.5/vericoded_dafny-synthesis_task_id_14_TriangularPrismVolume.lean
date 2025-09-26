import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  intro h_base h_height h_length
  unfold TriangularPrismVolume
  rfl
-- </vc-theorems>
