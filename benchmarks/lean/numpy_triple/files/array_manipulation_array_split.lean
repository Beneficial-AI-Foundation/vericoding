-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_split {n k : Nat} (v : Vector Float n) (hk : k > 0) : 
    Id (Vector (Σ m : Nat, Vector Float m) k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_split_spec {n k : Nat} (v : Vector Float n) (hk : k > 0) :
    ⦃⌜k > 0⌝⦄
    array_split v hk
    ⦃⇓result => ⌜
      -- Each sub-vector has the correct size based on its position
      (∀ i : Fin k, 
        (result.get i).1 = 
          if i.val < n % k then (n + k - 1) / k else n / k) ∧
      -- Elements are preserved in order across all sub-vectors
      (∃ (start_indices : Vector Nat k),
        -- First sub-vector starts at index 0
        start_indices.get ⟨0, by omega⟩ = 0 ∧
        -- Each subsequent sub-vector starts where the previous one ended
        (∀ i : Fin k, i.val > 0 → 
          start_indices.get i = start_indices.get ⟨i.val - 1, by omega⟩ + 
            (result.get ⟨i.val - 1, by omega⟩).1) ∧
        -- Elements match the original vector
        (∀ i : Fin k, ∀ j : Fin (result.get i).1,
          (result.get i).2.get j = 
            v.get ⟨start_indices.get i + j.val, by sorry⟩))
    ⌝⦄ := by
  sorry
-- </vc-theorems>