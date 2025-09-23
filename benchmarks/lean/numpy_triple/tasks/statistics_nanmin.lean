-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanmin {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    nanmin a
    ⦃⇓result => ⌜-- Case 1: If there exists at least one non-NaN element
                 ((∃ i : Fin (n + 1), ¬result.isNaN ∧ ¬(a.get i).isNaN) →
                   (∃ min_idx : Fin (n + 1), 
                     result = a.get min_idx ∧ 
                     ¬(a.get min_idx).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → result ≤ a.get j))) ∧
                 -- Case 2: If all elements are NaN, result is NaN
                 ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
                 -- Case 3: NaN values are ignored (result is min of non-NaN elements)
                 (¬result.isNaN → 
                   (∃ witness : Fin (n + 1), 
                     result = a.get witness ∧ 
                     ¬(a.get witness).isNaN ∧
                     (∀ j : Fin (n + 1), ¬(a.get j).isNaN → result ≤ a.get j))) ∧
                 -- Case 4: For vectors without NaN, behaves like regular min
                 ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
                   (∃ min_idx : Fin (n + 1),
                     result = a.get min_idx ∧
                     (∀ j : Fin (n + 1), result ≤ a.get j))) ∧
                 -- Sanity check: result is either NaN or exists in the vector
                 (result.isNaN ∨ (∃ witness : Fin (n + 1), result = a.get witness))⌝⦄ := by
  sorry
-- </vc-theorems>