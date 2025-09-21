-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NZERO : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem NZERO_spec :
    ⦃⌜True⌝⦄
    NZERO
    ⦃⇓result => ⌜
      -- Negative zero equals positive zero in value
      result = 0.0 ∧
      -- Basic arithmetic properties
      result + 0.0 = 0.0 ∧
      result - 0.0 = 0.0 ∧
      result * 1.0 = 0.0 ∧
      -- Multiplication by positive number preserves negative zero
      result * 2.0 = 0.0 ∧
      -- Division properties (note: in IEEE 754, 1.0 / -0.0 = -∞)
      result / 1.0 = 0.0 ∧
      -- Addition with positive numbers
      result + 1.0 = 1.0 ∧
      result + (-1.0) = -1.0 ∧
      -- Subtraction properties
      1.0 - result = 1.0 ∧
      (-1.0) - result = -1.0 ∧
      -- Absolute value of negative zero is positive zero
      Float.abs result = 0.0
    ⌝⦄ := by
  sorry
-- </vc-theorems>