import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_log10 {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_log10_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > 0⌝⦄
    numpy_log10 x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log10 (x.get i)⌝⦄ := by
  sorry
