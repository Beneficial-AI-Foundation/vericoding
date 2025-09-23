-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def copyto {n : Nat} {T : Type} (dst : Vector T n) (src : Vector T n) (mask : Vector Bool n) : Id (Vector T n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem copyto_spec {n : Nat} {T : Type} (dst : Vector T n) (src : Vector T n) (mask : Vector Bool n) :
    ⦃⌜True⌝⦄
    copyto dst src mask
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = if mask.get i then src.get i else dst.get i⌝⦄ := by
  sorry
-- </vc-theorems>