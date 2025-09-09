import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def True_ : Id Bool :=
  sorry

theorem True__spec :
    ⦃⌜True⌝⦄
    True_
    ⦃⇓result => ⌜result = true ∧ 
                 (∀ b : Bool, result && b = b) ∧
                 (∀ b : Bool, result || b = true) ∧
                 (!result = false)⌝⦄ := by
  sorry
