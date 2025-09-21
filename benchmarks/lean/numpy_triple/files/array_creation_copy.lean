-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def copy {n : Nat} (a : Vector α n) : Id (Vector α n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem copy_spec {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    copy a
    ⦃⇓result => ⌜∀ i : Fin n, result[i] = a[i]⌝⦄ := by
  sorry
-- </vc-theorems>