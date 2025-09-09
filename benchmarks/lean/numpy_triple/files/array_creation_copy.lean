import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def copy {n : Nat} (a : Vector α n) : Id (Vector α n) :=
  sorry

theorem copy_spec {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    copy a
    ⦃⇓result => ⌜∀ i : Fin n, result[i] = a[i]⌝⦄ := by
  sorry
