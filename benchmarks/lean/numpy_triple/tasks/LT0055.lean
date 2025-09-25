-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flipud {n : Nat} (m : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flipud_spec {n : Nat} (m : Vector Float n) :
    ⦃⌜True⌝⦄
    flipud m
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = m.get ⟨n - 1 - i.val, by 
                   have h : i.val < n := i.isLt
                   omega⟩⌝⦄ := by
  sorry
-- </vc-theorems>