import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ones_like {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) : Id (Vector T n) :=
  sorry

theorem ones_like_spec {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) :
    ⦃⌜True⌝⦄
    ones_like a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1⌝⦄ := by
  sorry
