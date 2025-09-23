-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def select {n : Nat} {k : Nat} (condlist : Vector (Vector Bool n) k) (choicelist : Vector (Vector Float n) k) (default : Float) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem select_spec {n : Nat} {k : Nat} (condlist : Vector (Vector Bool n) k) (choicelist : Vector (Vector Float n) k) (default : Float) :
    ⦃⌜True⌝⦄
    select condlist choicelist default
    ⦃⇓result => ⌜∀ i : Fin n, 
      (∃ j : Fin k, (condlist.get j).get i = true ∧ 
        result.get i = (choicelist.get j).get i ∧
        (∀ j' : Fin k, j' < j → (condlist.get j').get i = false)) ∨
      (∀ j : Fin k, (condlist.get j).get i = false ∧ result.get i = default)⌝⦄ := by
  sorry
-- </vc-theorems>