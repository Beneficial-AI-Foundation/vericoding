-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def identity (n : Nat) : Id (Vector (Vector Float n) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_spec (n : Nat) :
    ⦃⌜True⌝⦄
    identity n
    ⦃⇓result => ⌜∀ i j : Fin n, 
                   (result.get i).get j = if i = j then (1.0 : Float) else (0.0 : Float)⌝⦄ := by
  sorry
-- </vc-theorems>