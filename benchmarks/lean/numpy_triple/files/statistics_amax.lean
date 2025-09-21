-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def amax {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem amax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    amax a
    ⦃⇓result => ⌜-- Core property: result is the maximum element in the vector
                 (∃ max_idx : Fin (n + 1),
                   result = a.get max_idx ∧
                   (∀ i : Fin (n + 1), a.get i ≤ result)) ∧
                 -- Uniqueness: result is the first occurrence of the maximum
                 (∃ first_max_idx : Fin (n + 1),
                   result = a.get first_max_idx ∧
                   (∀ i : Fin (n + 1), a.get i = result → first_max_idx ≤ i) ∧
                   (∀ i : Fin (n + 1), a.get i ≤ result)) ∧
                 -- For constant vectors, amax equals the constant
                 ((∀ i j : Fin (n + 1), a.get i = a.get j) → 
                   result = a.get ⟨0, Nat.zero_lt_succ n⟩) ∧
                 -- Sanity check: the maximum exists in the vector
                 (∃ witness : Fin (n + 1), result = a.get witness)⌝⦄ := by
  sorry
-- </vc-theorems>