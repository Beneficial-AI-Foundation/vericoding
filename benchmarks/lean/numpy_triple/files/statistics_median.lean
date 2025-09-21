-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def median {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem median_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    median a
    ⦃⇓m => ⌜∃ sorted : Vector Float (n + 1),
            -- sorted is a permutation of a
            (∀ i : Fin (n + 1), ∃ j : Fin (n + 1), sorted.get i = a.get j) ∧
            (∀ j : Fin (n + 1), ∃ i : Fin (n + 1), sorted.get i = a.get j) ∧
            -- sorted is in non-decreasing order
            (∀ i j : Fin (n + 1), i < j → sorted.get i ≤ sorted.get j) ∧
            -- m is the median of sorted based on odd/even length
            (if h : (n + 1) % 2 = 1 then
              -- odd case: middle element at index n/2
              m = sorted.get ⟨n / 2, by
                have : n / 2 < n + 1 :=
  sorry
                exact this⟩
            else
              -- even case: average of two middle elements  
              m = (sorted.get ⟨n / 2, by
                have : n / 2 < n + 1 :=
  sorry
                exact this⟩ + 
                   sorted.get ⟨(n + 1) / 2, by
                have : (n + 1) / 2 < n + 1 :=
  sorry
                exact this⟩) / 2) ∧
            -- median property: it's a value that appears in the original vector
            -- or can be computed from values in the vector
            (∃ i : Fin (n + 1), m = sorted.get i ∨ 
             ∃ i j : Fin (n + 1), m = (sorted.get i + sorted.get j) / 2)⌝⦄ := by
  sorry
-- </vc-theorems>