-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def histogram {n_data n_bins : Nat} (data : Vector Float n_data) (min_val max_val : Float)
    (h_bins_pos : n_bins > 0) (h_range : min_val < max_val) : 
    Id (Vector Nat n_bins × Vector Float (n_bins + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem histogram_spec {n_data n_bins : Nat} (data : Vector Float n_data) (min_val max_val : Float)
    (h_bins_pos : n_bins > 0) (h_range : min_val < max_val) :
    ⦃⌜n_bins > 0 ∧ min_val < max_val⌝⦄
    histogram data min_val max_val h_bins_pos h_range
    ⦃⇓result => ⌜-- Bin edges are monotonically increasing
      (∀ i j : Fin (n_bins + 1), i.val < j.val → result.2.get i < result.2.get j) ∧
      -- Boundary conditions: first edge is min_val, last edge is max_val
      (result.2.get ⟨0, Nat.succ_pos n_bins⟩ = min_val) ∧
      (result.2.get ⟨n_bins, Nat.le_refl (n_bins + 1)⟩ = max_val) ∧
      -- Uniform binning: all bin widths are equal
      (∀ i : Fin n_bins, 
        result.2.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ - 
        result.2.get ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n_bins)⟩ = 
        (max_val - min_val) / n_bins.toFloat) ∧
      -- Each bin count is non-negative (trivially true for Nat)
      (∀ i : Fin n_bins, result.1.get i ≥ 0) ∧
      -- Conservation: total count equals number of data points in range
      (List.sum (List.map result.1.get (List.finRange n_bins)) = 
        (data.toList.filter (fun x => min_val ≤ x ∧ x ≤ max_val)).length)⌝⦄ := by
  sorry
-- </vc-theorems>