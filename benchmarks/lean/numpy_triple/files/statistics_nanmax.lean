-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanmax {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    nanmax a
    ⦃⇓result => ⌜-- Case 1: If there exists at least one non-NaN element
                 ((∃ i : Fin (n + 1), ¬result.isNaN ∧ ¬(a.get i).isNaN) →
                   (∃ max_idx : Fin (n + 1), 
                     result = a.get max_idx ∧ 
                     ¬(a.get max_idx).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
                 -- Case 2: If all elements are NaN, result is NaN
                 ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
                 -- Case 3: NaN values are ignored (result is max of non-NaN elements)
                 (¬result.isNaN → 
                   (∃ witness : Fin (n + 1), 
                     result = a.get witness ∧ 
                     ¬(a.get witness).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
                 -- Case 4: For vectors without NaN, behaves like regular max
                 ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
                   (∃ max_idx : Fin (n + 1),
                     result = a.get max_idx ∧
                     (∀ j : Fin (n + 1), a.get j ≤ result))) ∧
                 -- Sanity check: result is either NaN or exists in the vector
                 (result.isNaN ∨ (∃ witness : Fin (n + 1), result = a.get witness))⌝⦄ := by
  sorry
-- </vc-theorems>