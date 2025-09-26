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
by intros _ _ _; rfl
-- </vc-theorems>
