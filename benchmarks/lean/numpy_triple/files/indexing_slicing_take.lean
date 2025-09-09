import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def take {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) : Id (Vector Float m) :=
  sorry

theorem take_spec {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) :
    ⦃⌜True⌝⦄
    take arr indices
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = arr.get (indices.get i)⌝⦄ := by
  sorry
