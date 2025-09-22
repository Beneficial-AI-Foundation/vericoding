-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanmedian {n : Nat} (a : Vector Float n) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanmedian_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    nanmedian a
    ⦃⇓result => ⌜
      -- Case 1: All values are NaN
      (∀ i : Fin n, (a.get i).isNaN) → result.isNaN ∧
      -- Case 2: At least one finite value exists
      (∃ i : Fin n, ¬(a.get i).isNaN) → 
        ∃ finite_indices : List (Fin n),
          -- finite_indices contains all indices with finite values
          (∀ i : Fin n, i ∈ finite_indices ↔ ¬(a.get i).isNaN) ∧
          finite_indices.length > 0 ∧
          -- There exists a sorted permutation of finite values
          ∃ sorted_vals : List Float,
            -- sorted_vals is the sorted list of finite values
            sorted_vals.length = finite_indices.length ∧
            (∀ i : Fin finite_indices.length, 
              sorted_vals.get ⟨i, sorry⟩ = a.get (finite_indices.get ⟨i, sorry⟩)) ∧
            -- sorted_vals is in non-decreasing order
            (∀ i j : Fin sorted_vals.length, i < j → 
              sorted_vals.get ⟨i, sorry⟩ ≤ sorted_vals.get ⟨j, sorry⟩) ∧
            -- result is the median of sorted finite values
            (if sorted_vals.length % 2 = 1 then
              result = sorted_vals.get ⟨sorted_vals.length / 2, sorry⟩
            else
              result = (sorted_vals.get ⟨sorted_vals.length / 2 - 1, sorry⟩ + 
                       sorted_vals.get ⟨sorted_vals.length / 2, sorry⟩) / 2)
    ⌝⦄ := by
  sorry
-- </vc-theorems>