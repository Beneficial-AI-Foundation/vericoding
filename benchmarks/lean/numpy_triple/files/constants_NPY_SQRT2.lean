/- 
{
  "name": "NPY_SQRT2",
  "category": "C API Mathematical constants",
  "description": "Square root of 2",
  "doc": "√2 = 1.414213562373095048801688724209698079",
}
-/

/-  The square root of 2 as a mathematical constant -/

/-  Specification: NPY_SQRT2 represents the square root of 2 with appropriate mathematical properties -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def NPY_SQRT2 : Id Float :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem NPY_SQRT2_spec :
    ⦃⌜True⌝⦄
    NPY_SQRT2
    ⦃⇓result => ⌜
      -- Sanity check: result is positive
      result > 0 ∧
      -- Mathematical property: result squared equals 2 (within floating-point precision)
      Float.abs (result * result - 2.0) < 1e-15 ∧
      -- Value check: result is approximately 1.414213562373095
      Float.abs (result - 1.414213562373095048801688724209698079) < 1e-15
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
