-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def philox {n : Nat} (seed : Nat) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem philox_spec {n : Nat} (seed : Nat) :
    ⦃⌜True⌝⦄
    philox seed
    ⦃⇓result => ⌜(∀ i : Fin n, 0 ≤ result.get i ∧ result.get i < 1) ∧
                  (∀ seed₁ seed₂ : Nat, seed₁ = seed₂ → (philox seed₁ : Id (Vector Float n)) = (philox seed₂ : Id (Vector Float n)))⌝⦄ := by
  sorry
-- </vc-theorems>