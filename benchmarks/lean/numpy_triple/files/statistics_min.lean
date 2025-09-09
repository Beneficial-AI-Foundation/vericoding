import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def min {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry

theorem min_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    min a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  sorry
