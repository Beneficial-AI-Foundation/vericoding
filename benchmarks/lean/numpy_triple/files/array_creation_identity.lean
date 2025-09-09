import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def identity (n : Nat) : Id (Vector (Vector Float n) n) :=
  sorry

theorem identity_spec (n : Nat) :
    ⦃⌜True⌝⦄
    identity n
    ⦃⇓result => ⌜∀ i j : Fin n, 
                   (result.get i).get j = if i = j then (1.0 : Float) else (0.0 : Float)⌝⦄ := by
  sorry
