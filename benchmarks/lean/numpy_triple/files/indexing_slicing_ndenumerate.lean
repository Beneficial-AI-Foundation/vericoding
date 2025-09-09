import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ndenumerate {n : Nat} (arr : Vector Float n) : Id (Vector (Fin n × Float) n) :=
  sorry

theorem ndenumerate_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    ndenumerate arr
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (i, arr.get i)⌝⦄ := by
  sorry
