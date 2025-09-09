import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def invert {n : Nat} (x : Vector Int n) : Id (Vector Int n) :=
  sorry

theorem invert_spec {n : Nat} (x : Vector Int n) :
    ⦃⌜True⌝⦄
    invert x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = -(x.get i + 1)) ∧
                 (result.size = n) ∧
                 (∀ i : Fin n, x.get i = 0 → result.get i = -1) ∧
                 (∀ i : Fin n, x.get i = -1 → result.get i = 0) ∧
                 (∀ i : Fin n, x.get i ≠ -1 → (x.get i > 0 ↔ result.get i < 0))⌝⦄ := by
  sorry
