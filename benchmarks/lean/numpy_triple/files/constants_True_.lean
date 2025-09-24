-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def True_ : Id Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem True__spec :
    ⦃⌜True⌝⦄
    True_
    ⦃⇓result => ⌜result = true ∧ 
                 (∀ b : Bool, result && b = b) ∧
                 (∀ b : Bool, result || b = true) ∧
                 (!result = false)⌝⦄ := by
  sorry
-- </vc-theorems>