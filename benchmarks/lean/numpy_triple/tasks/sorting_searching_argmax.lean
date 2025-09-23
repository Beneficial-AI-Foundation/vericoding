-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def argmax {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem argmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get j ≤ a.get i) ∧ 
            (∀ j : Fin (n + 1), a.get j = a.get i → i ≤ j)⌝⦄ := by
  sorry
-- </vc-theorems>