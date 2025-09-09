import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def NPY_PI_4 : Id Float :=
  sorry

theorem NPY_PI_4_spec :
    ⦃⌜True⌝⦄
    NPY_PI_4
    ⦃⇓result => ⌜result = 0.785398163397448309615660845819875721 ∧
                  result > 0.785 ∧ result < 0.786 ∧
                  result * 4 > 3.141 ∧ result * 4 < 3.142⌝⦄ := by
  sorry
