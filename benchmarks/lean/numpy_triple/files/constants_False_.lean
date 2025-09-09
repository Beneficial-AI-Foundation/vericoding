import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def False_ : Id Bool :=
  sorry

theorem False__spec :
    ⦃⌜True⌝⦄
    False_
    ⦃⇓result => ⌜result = false ∧ 
                 (∀ b : Bool, result || b = b) ∧
                 (∀ b : Bool, result && b = false) ∧
                 result = !true⌝⦄ := by
  sorry
