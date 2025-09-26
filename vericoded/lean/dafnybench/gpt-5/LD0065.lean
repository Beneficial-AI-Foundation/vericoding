import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
noncomputable instance : Coe Prop Bool where
  coe p := by
    classical
    exact decide p
-- </vc-helpers>

-- <vc-definitions>
def ComputeIsEven (x : Int) : Bool :=
decide (x % 2 = 0)
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeIsEven_spec (x : Int) :
ComputeIsEven x = (x % 2 = 0) :=
rfl
-- </vc-theorems>
