import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def argmax {n : Nat} (arr : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

theorem argmax_spec {n : Nat} (arr : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax arr
    ⦃⇓idx => ⌜(∀ i : Fin (n + 1), arr.get i ≤ arr.get idx) ∧
             (∀ i : Fin (n + 1), i < idx → arr.get i < arr.get idx) ∧
             (∀ i : Fin (n + 1), idx < i → arr.get i ≤ arr.get idx) ∧
             (∀ j : Fin (n + 1), arr.get j = arr.get idx → idx ≤ j)⌝⦄ := by
  sorry
