-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NPY_SQRT2 : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
  sorry
-- </vc-theorems>