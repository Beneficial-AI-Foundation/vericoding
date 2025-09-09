import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def bitwise_and {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry

theorem bitwise_and_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0⌝⦄
    bitwise_and x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.toNat (x1.get i) &&& Int.toNat (x2.get i))) ∧
                (∀ i : Fin n, result.get i ≥ 0) ∧
                (∀ i : Fin n, result.get i ≤ x1.get i) ∧
                (∀ i : Fin n, result.get i ≤ x2.get i) ∧
                (∀ i : Fin n, result.get i = 0 ↔ (x1.get i = 0 ∨ x2.get i = 0)) ∧
                (∀ i : Fin n, x1.get i = x2.get i → result.get i = x1.get i)⌝⦄ := by
  sorry
