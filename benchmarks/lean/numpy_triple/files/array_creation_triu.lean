-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def triu {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    Id (Vector (Vector Float cols) rows) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triu_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    ⦃⌜True⌝⦄
    triu m k
    ⦃⇓result => ⌜(∀ (i : Fin rows) (j : Fin cols), 
                   (result.get i).get j = 
                     if (i.val : Int) > (j.val : Int) - k then 0 
                     else (m.get i).get j) ∧
                  (∀ (i : Fin rows) (j : Fin cols),
                   (i.val : Int) ≤ (j.val : Int) - k → 
                   (result.get i).get j = (m.get i).get j) ∧
                  (∀ (i : Fin rows) (j : Fin cols),
                   (i.val : Int) > (j.val : Int) - k → 
                   (result.get i).get j = 0)⌝⦄ := by
  sorry
-- </vc-theorems>