import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def r_ {n m : Nat} (a : Vector Float n) (b : Vector Float m) : 
    Id (Vector Float (n + m)) :=
  sorry

theorem r__spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    ⦃⌜True⌝⦄
    r_ a b
    ⦃⇓result => ⌜(∀ i : Fin n, result.get (i.castAdd m) = a.get i) ∧
                 (∀ j : Fin m, result.get (j.natAdd n) = b.get j)⌝⦄ := by
  sorry
