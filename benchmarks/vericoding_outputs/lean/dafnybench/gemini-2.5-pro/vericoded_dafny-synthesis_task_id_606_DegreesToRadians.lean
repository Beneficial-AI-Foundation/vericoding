import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
namespace MyMath
/-- The mathematical constant pi, as a Float. -/
def pi : Float := 3.141592653589793
end MyMath
-- </vc-helpers>

-- <vc-definitions>
def DegreesToRadians (degrees : Float ) : Float :=
degrees * MyMath.pi / 180
-- </vc-definitions>

-- <vc-theorems>
theorem DegreesToRadians_spec (degrees : Float) :
DegreesToRadians degrees = degrees * 3.141592653589793 / 180 :=
rfl
-- </vc-theorems>
