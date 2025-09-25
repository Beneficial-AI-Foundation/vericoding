-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanquantile {n : Nat} (a : Vector Float (n + 1)) (q : Float) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanquantile_spec {n : Nat} (a : Vector Float (n + 1)) (q : Float) 
    (h_q_valid : 0 ≤ q ∧ q ≤ 1) :
    ⦃⌜0 ≤ q ∧ q ≤ 1⌝⦄
    nanquantile a q
    ⦃⇓result => 
      ⌜-- Case 1: If there exists at least one non-NaN element
       ((∃ i : Fin (n + 1), ¬(a.get i).isNaN) →
         (¬result.isNaN ∧
          -- Result is bounded by the non-NaN elements
          (∃ min_idx : Fin (n + 1), ¬(a.get min_idx).isNaN ∧ 
            (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get min_idx ≤ a.get j) ∧
            a.get min_idx ≤ result) ∧
          (∃ max_idx : Fin (n + 1), ¬(a.get max_idx).isNaN ∧ 
            (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ a.get max_idx) ∧
            result ≤ a.get max_idx))) ∧
       -- Case 2: If all elements are NaN, result is NaN
       ((∀ i : Fin (n + 1), (a.get i).isNaN) → result.isNaN) ∧
       -- Case 3: For q=0, result is the minimum of non-NaN elements
       (q = 0 → (∃ i : Fin (n + 1), ¬(a.get i).isNaN) → 
         (∃ min_idx : Fin (n + 1), 
           result = a.get min_idx ∧ 
           ¬(a.get min_idx).isNaN ∧
           (∀ j : Fin (n + 1), ¬(a.get j).isNaN → result ≤ a.get j))) ∧
       -- Case 4: For q=1, result is the maximum of non-NaN elements
       (q = 1 → (∃ i : Fin (n + 1), ¬(a.get i).isNaN) → 
         (∃ max_idx : Fin (n + 1), 
           result = a.get max_idx ∧ 
           ¬(a.get max_idx).isNaN ∧
           (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ result))) ∧
       -- Case 5: For vectors without NaN, behaves like regular quantile
       ((∀ i : Fin (n + 1), ¬(a.get i).isNaN) → 
         (¬result.isNaN ∧
          (∃ lower_idx upper_idx : Fin (n + 1),
            a.get lower_idx ≤ result ∧ result ≤ a.get upper_idx)))⌝⦄ := by
  sorry
-- </vc-theorems>