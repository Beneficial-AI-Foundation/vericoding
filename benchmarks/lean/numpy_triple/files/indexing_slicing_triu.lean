-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def triu {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) : Id (Vector (Vector Float cols) rows) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triu_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    ⦃⌜True⌝⦄
    triu m k
    ⦃⇓result => ⌜
      (∀ i : Fin rows, ∀ j : Fin cols, (i.val : Int) + k ≤ (j.val : Int) → 
        (result.get i).get j = (m.get i).get j) ∧
      (∀ i : Fin rows, ∀ j : Fin cols, (i.val : Int) + k > (j.val : Int) → 
        (result.get i).get j = (0 : Float))⌝⦄ := by
  sorry
-- </vc-theorems>