-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanpercentile {n : Nat} (a : Vector Float n) (q : Float) (h : 0 ≤ q ∧ q ≤ 100) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanpercentile_spec {n : Nat} (a : Vector Float n) (q : Float) (h : 0 ≤ q ∧ q ≤ 100) :
    ⦃⌜0 ≤ q ∧ q ≤ 100⌝⦄
    nanpercentile a q h
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
            -- Percentile computation: q% of sorted values
            (if sorted_vals.length = 1 then
               -- Single value case
               result = sorted_vals.get ⟨0, sorry⟩
             else
               -- For any percentile q, the result should be within the range
               -- of the sorted values and satisfy the percentile property
               ∃ idx : Nat, 
                 idx < sorted_vals.length ∧
                 result = sorted_vals.get ⟨idx, sorry⟩ ∨
                 -- OR result is an interpolated value between two consecutive elements
                 (∃ i j : Nat, 
                   i < sorted_vals.length ∧ j < sorted_vals.length ∧
                   i + 1 = j ∧
                   sorted_vals.get ⟨i, sorry⟩ ≤ result ∧
                   result ≤ sorted_vals.get ⟨j, sorry⟩)) ∧
            -- Sanity checks: result should be within bounds of finite values
            (¬result.isNaN → 
              sorted_vals.get ⟨0, sorry⟩ ≤ result ∧ 
              result ≤ sorted_vals.get ⟨sorted_vals.length - 1, sorry⟩)
    ⌝⦄ := by
  sorry
-- </vc-theorems>