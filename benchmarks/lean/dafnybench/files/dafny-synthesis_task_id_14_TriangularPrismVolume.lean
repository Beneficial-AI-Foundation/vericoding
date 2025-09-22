-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def TriangularPrismVolume (base : Int) (height : Int) (length : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem TriangularPrismVolume_spec (base height length : Int) :
base > 0 →
height > 0 →
length > 0 →
TriangularPrismVolume base height length = (base * height * length) / 2 :=
sorry
-- </vc-theorems>