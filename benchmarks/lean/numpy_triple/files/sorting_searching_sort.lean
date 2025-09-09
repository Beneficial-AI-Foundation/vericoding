import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def sort {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem sort_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    sort a
    ⦃⇓result => ⌜(∀ i j : Fin n, i.val < j.val → result.get i ≤ result.get j) ∧
                (∀ x : Float, (result.toList.count x) = (a.toList.count x))⌝⦄ := by
  sorry
