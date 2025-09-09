import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def stack {m n : Nat} (arrays : Vector (Vector Float n) m) : Id (Vector (Vector Float n) m) :=
  sorry

theorem stack_spec {m n : Nat} (arrays : Vector (Vector Float n) m) :
    ⦃⌜True⌝⦄
    stack arrays
    ⦃⇓result => ⌜∀ i : Fin m, ∀ j : Fin n, 
                  (result.get i).get j = (arrays.get i).get j⌝⦄ := by
  sorry
