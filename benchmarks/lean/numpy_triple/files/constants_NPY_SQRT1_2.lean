/- 
{
  "name": "NPY_SQRT1_2",
  "category": "C API Mathematical constants",
  "description": "Square root of 1/2",
  "doc": "√(1/2) = 0.707106781186547524400844362104849039",
}
-/

/-  NPY_SQRT1_2: Square root of 1/2 as a Float constant -/

/-  Specification: NPY_SQRT1_2 equals the square root of 1/2 with mathematical properties -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def NPY_SQRT1_2 : Id Float :=
  sorry

theorem NPY_SQRT1_2_spec :
    ⦃⌜True⌝⦄
    NPY_SQRT1_2
    ⦃⇓result => ⌜result * result = 0.5 ∧ 
                 result > 0 ∧
                 result = Float.sqrt 0.5 ∧
                 result = 1.0 / Float.sqrt 2.0 ∧
                 Float.abs (result - 0.707106781186547524400844362104849039) < 1e-15⌝⦄ := by
  sorry
