import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def DegreesToRadians (degrees : Float ) : Float :=
degrees * 3.141592653589793 / 180
-- </vc-definitions>

-- <vc-theorems>
theorem DegreesToRadians_spec (degrees : Float) :
DegreesToRadians degrees = degrees * 3.141592653589793 / 180 :=
by rfl
-- </vc-theorems>
