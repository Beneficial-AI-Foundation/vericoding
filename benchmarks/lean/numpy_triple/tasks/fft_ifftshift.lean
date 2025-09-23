-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ifftshift {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ifftshift_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    ifftshift x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x.get ⟨(i.val + n / 2) % n, sorry⟩⌝⦄ := by
  sorry
-- </vc-theorems>