-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NPY_PI_2 : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem NPY_PI_2_spec :
    ⦃⌜True⌝⦄
    NPY_PI_2
    ⦃⇓result => ⌜
      -- π/2 is approximately 1.5708...
      1.5707 < result ∧ result < 1.5708 ∧
      -- Basic sanity check: π/2 is between 1 and 2
      1 < result ∧ result < 2 ∧
      -- π/2 squared is approximately 2.4674...
      2.467 < result * result ∧ result * result < 2.468 ∧
      -- 2*(π/2) should be approximately π (3.14159...)
      3.141 < 2 * result ∧ 2 * result < 3.142 ∧
      -- (π/2)/2 = π/4 is approximately 0.7854...
      0.785 < result / 2 ∧ result / 2 < 0.786 ∧
      -- 3*(π/2) = 3π/2 is approximately 4.7124... (270 degrees)
      4.712 < 3 * result ∧ 3 * result < 4.713 ∧
      -- 4*(π/2) = 2π is approximately 6.2832... (full circle)
      6.283 < 4 * result ∧ 4 * result < 6.284
    ⌝⦄ := by
  sorry
-- </vc-theorems>