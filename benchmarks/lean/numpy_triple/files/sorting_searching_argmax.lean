import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def argmax {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

theorem argmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get j ≤ a.get i) ∧ 
            (∀ j : Fin (n + 1), a.get j = a.get i → i ≤ j)⌝⦄ := by
  sorry
