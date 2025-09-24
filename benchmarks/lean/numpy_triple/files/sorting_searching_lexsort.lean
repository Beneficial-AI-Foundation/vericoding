-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lexsort {n k : Nat} (keys : Vector (Vector Float n) k) (h : k > 0) : Id (Vector (Fin n) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lexsort_spec {n k : Nat} (keys : Vector (Vector Float n) k) (h : k > 0) :
    ⦃⌜k > 0⌝⦄
    lexsort keys h
    ⦃⇓indices => ⌜
      -- indices is a permutation of 0..n-1
      (∀ i : Fin n, ∃ j : Fin n, indices.get j = i) ∧
      (∀ i j : Fin n, indices.get i = indices.get j → i = j) ∧
      -- lexicographic ordering property
      (∀ i j : Fin n, i < j → 
        ∃ key_idx : Fin k, 
          -- All keys from key_idx+1 to k-1 are equal
          (∀ l : Fin k, key_idx < l → 
            (keys.get l).get (indices.get i) = (keys.get l).get (indices.get j)) ∧
          -- Key at key_idx determines the order
          (keys.get key_idx).get (indices.get i) ≤ (keys.get key_idx).get (indices.get j)) ∧
      -- stability property: if all keys are equal, preserve original order
      (∀ i j : Fin n, i < j → 
        (∀ l : Fin k, (keys.get l).get i = (keys.get l).get j) → 
        ∃ p q : Fin n, indices.get p = i ∧ indices.get q = j ∧ p < q)
    ⌝⦄ := by
  sorry
-- </vc-theorems>