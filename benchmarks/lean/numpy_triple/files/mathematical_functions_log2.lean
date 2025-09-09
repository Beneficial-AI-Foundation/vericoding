import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def log2 {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem log2_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > 0⌝⦄
    log2 x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log2 (x.get i)⌝⦄ := by
  sorry
