import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Approximation of π as a Float used by conversions.
def PI_APPROX : Float := 3.141592653589793
-- </vc-helpers>

-- <vc-definitions>
def DegreesToRadians (degrees : Float ) : Float :=
degrees * PI_APPROX / 180
-- </vc-definitions>

-- <vc-theorems>
theorem DegreesToRadians_spec (degrees : Float) :
DegreesToRadians degrees = degrees * 3.141592653589793 / 180 :=
by
  simp [DegreesToRadians, PI_APPROX]
-- </vc-theorems>
