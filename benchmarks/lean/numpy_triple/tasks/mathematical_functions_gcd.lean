-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_gcd {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_gcd_spec {n : Nat} (x1 x2 : Vector Int n) :
    ⦃⌜True⌝⦄
    numpy_gcd x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.gcd (x1.get i) (x2.get i))) ∧
                 (∀ i : Fin n, result.get i ≥ 0) ∧
                 (∀ i : Fin n, Int.gcd (x1.get i) (x2.get i) = (x1.get i).natAbs.gcd (x2.get i).natAbs) ∧
                 (∀ i : Fin n, (x1.get i = 0 ∧ x2.get i = 0) → result.get i = 0) ∧
                 (∀ i : Fin n, (x1.get i ≠ 0 ∧ x2.get i = 0) → result.get i = Int.natAbs (x1.get i)) ∧
                 (∀ i : Fin n, (x1.get i = 0 ∧ x2.get i ≠ 0) → result.get i = Int.natAbs (x2.get i)) ∧
                 (∀ i : Fin n, result.get i ∣ (x1.get i) ∧ result.get i ∣ (x2.get i)) ∧
                 (∀ i : Fin n, ∀ (d : Int), d ∣ (x1.get i) → d ∣ (x2.get i) → d ∣ result.get i) ∧
                 (∀ i : Fin n, Int.gcd (x2.get i) (x1.get i) = Int.gcd (x1.get i) (x2.get i))⌝⦄ := by
  sorry
-- </vc-theorems>