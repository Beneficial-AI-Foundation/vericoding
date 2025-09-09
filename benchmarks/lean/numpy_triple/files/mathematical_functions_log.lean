import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def log {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem log_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > 0⌝⦄
    log x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log (x.get i)⌝⦄ := by
  sorry
