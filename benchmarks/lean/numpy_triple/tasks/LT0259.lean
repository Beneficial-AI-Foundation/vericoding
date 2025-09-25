-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bitwise_xor {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bitwise_xor_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0⌝⦄
    bitwise_xor x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.toNat (x1.get i) ^^^ Int.toNat (x2.get i))) ∧
                (∀ i : Fin n, result.get i ≥ 0) ∧
                (∀ i : Fin n, x1.get i = 0 → result.get i = x2.get i) ∧
                (∀ i : Fin n, x2.get i = 0 → result.get i = x1.get i) ∧
                (∀ i : Fin n, x1.get i = x2.get i → result.get i = 0)⌝⦄ := by
  sorry
-- </vc-theorems>