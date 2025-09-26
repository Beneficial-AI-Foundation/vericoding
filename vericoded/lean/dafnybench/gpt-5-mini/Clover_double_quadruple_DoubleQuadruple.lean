import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/- No helpers required for this simple example. -/
-- </vc-helpers>

-- <vc-definitions>
def DoubleQuadruple (x : Int) : Int × Int :=
(2 * x, 4 * x)
-- </vc-definitions>

-- <vc-theorems>
theorem DoubleQuadruple_spec (x : Int) :
let (a, b) := DoubleQuadruple x
a = 2 * x ∧ b = 4 * x :=
by
  have h : DoubleQuadruple x = (2 * x, 4 * x) := rfl
  simp [h]
-- </vc-theorems>
