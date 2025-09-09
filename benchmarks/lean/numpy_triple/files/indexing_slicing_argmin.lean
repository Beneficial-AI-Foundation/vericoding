import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def argmin {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

theorem argmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmin a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get i ≤ a.get j) ∧ 
           (∀ k : Fin (n + 1), k < i → a.get k > a.get i)⌝⦄ := by
  sorry
