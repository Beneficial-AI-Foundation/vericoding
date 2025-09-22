-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nonzero {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nonzero_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    nonzero a
    ⦃⇓indices => ⌜(∀ i ∈ indices, a.get i ≠ 0) ∧
                   (∀ j : Fin n, a.get j ≠ 0 → j ∈ indices) ∧
                   (∀ i₁ i₂ : Fin n, i₁ ∈ indices → i₂ ∈ indices → i₁ < i₂ → 
                    (indices.idxOf i₁ < indices.idxOf i₂)) ∧
                   (indices.Nodup)⌝⦄ := by
  sorry
-- </vc-theorems>