import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Pi constant for degree conversion
def pi : Float := 3.141592653589793
-- </vc-helpers>

-- <vc-definitions>
def DegreesToRadians (degrees : Float ) : Float :=
degrees * pi / 180
-- </vc-definitions>

-- <vc-theorems>
theorem DegreesToRadians_spec (degrees : Float) :
DegreesToRadians degrees = degrees * 3.141592653589793 / 180 :=
by
  unfold DegreesToRadians pi
  rfl
-- </vc-theorems>
