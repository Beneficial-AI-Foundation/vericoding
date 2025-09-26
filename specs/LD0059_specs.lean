-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DoubleQuadruple (x : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem DoubleQuadruple_spec (x : Int) :
let (a, b) := DoubleQuadruple x
a = 2 * x ∧ b = 4 * x :=
sorry
-- </vc-theorems>