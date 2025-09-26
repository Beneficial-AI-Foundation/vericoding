-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mapdomain {n : Nat} (x : Vector Float n) (old new : Vector Float 2) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mapdomain_spec {n : Nat} (x : Vector Float n) (old new : Vector Float 2)
    (h_nondegenerate : old.get 1 ≠ old.get 0) :
    ⦃⌜old.get 1 ≠ old.get 0⌝⦄
    mapdomain x old new
    ⦃⇓result => ⌜∀ i : Fin n, 
      let scale := (new.get 1 - new.get 0) / (old.get 1 - old.get 0)
      let offset := new.get 0 - scale * old.get 0
      result.get i = offset + scale * x.get i⌝⦄ := by
  sorry
-- </vc-theorems>