-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyvalfromroots {n m : Nat} (x : Vector Float n) (r : Vector Float m) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyvalfromroots_spec {n m : Nat} (x : Vector Float n) (r : Vector Float m) :
    ⦃⌜True⌝⦄
    polyvalfromroots x r
    ⦃⇓result => ⌜∀ i : Fin n, 
                  result.get i = (List.range m).foldl (fun acc j => acc * (x.get i - r.get ⟨j, sorry⟩)) 1⌝⦄ := by
  sorry
-- </vc-theorems>