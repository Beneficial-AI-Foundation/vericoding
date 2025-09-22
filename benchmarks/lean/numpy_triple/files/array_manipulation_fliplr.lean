-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fliplr {rows cols : Nat} (m : Vector (Vector Float cols) rows) : Id (Vector (Vector Float cols) rows) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fliplr_spec {rows : Nat} {cols : Nat} (m : Vector (Vector Float (cols + 1)) rows) :
    ⦃⌜True⌝⦄
    fliplr m
    ⦃⇓result => ⌜(∀ i : Fin rows, ∀ j : Fin (cols + 1), 
                   ∃ k : Fin (cols + 1), 
                   (result.get i).get j = (m.get i).get k ∧ 
                   j.val + k.val = cols) ∧
                 (∀ i : Fin rows, 
                   (∀ x : Float, (∃ j : Fin (cols + 1), (m.get i).get j = x) ↔ 
                                 (∃ j : Fin (cols + 1), (result.get i).get j = x))) ∧
                 (cols % 2 = 0 → 
                   ∀ i : Fin rows, 
                   ∃ mid : Fin (cols + 1),
                   2 * mid.val = cols ∧
                   (result.get i).get mid = (m.get i).get mid)⌝⦄ := by
  sorry
-- </vc-theorems>