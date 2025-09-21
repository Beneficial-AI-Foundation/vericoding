-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NPY_SQRT1_2 : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem NPY_SQRT1_2_spec :
    ⦃⌜True⌝⦄
    NPY_SQRT1_2
    ⦃⇓result => ⌜result * result = 0.5 ∧ 
                 result > 0 ∧
                 result = Float.sqrt 0.5 ∧
                 result = 1.0 / Float.sqrt 2.0 ∧
                 Float.abs (result - 0.707106781186547524400844362104849039) < 1e-15⌝⦄ := by
  sorry
-- </vc-theorems>