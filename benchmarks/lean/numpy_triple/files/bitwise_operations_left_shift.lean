import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def left_shift {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry

theorem left_shift_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x2.get i ≥ 0⌝⦄
    left_shift x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = x1.get i * (2 ^ (x2.get i).toNat)) ∧
                 (∀ i : Fin n, x2.get i = 0 → result.get i = x1.get i) ∧
                 (∀ i : Fin n, x1.get i = 0 → result.get i = 0) ∧
                 (∀ i : Fin n, x1.get i > 0 ∧ x2.get i > 0 → result.get i > x1.get i) ∧
                 (∀ i : Fin n, x1.get i < 0 ∧ x2.get i > 0 → result.get i < x1.get i)⌝⦄ := by
  sorry
