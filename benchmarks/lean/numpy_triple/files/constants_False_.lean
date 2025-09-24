-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def False_ : Id Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem False__spec :
    ⦃⌜True⌝⦄
    False_
    ⦃⇓result => ⌜result = false ∧ 
                 (∀ b : Bool, result || b = b) ∧
                 (∀ b : Bool, result && b = false) ∧
                 result = !true⌝⦄ := by
  sorry
-- </vc-theorems>