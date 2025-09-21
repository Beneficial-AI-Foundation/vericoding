-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def histogram_bin_edges {n : Nat} (data : Vector Float (n + 1)) (num_bins : Nat) 
    (h_bins : num_bins > 0) : Id (Vector Float (num_bins + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem histogram_bin_edges_spec {n : Nat} (data : Vector Float (n + 1)) (num_bins : Nat)
    (h_bins : num_bins > 0) :
    ⦃⌜num_bins > 0⌝⦄
    histogram_bin_edges data num_bins h_bins
    ⦃⇓edges => ⌜-- The returned edges have the correct length
                (edges.size = num_bins + 1) ∧
                -- The edges are monotonically increasing
                (∀ i : Fin num_bins, 
                  let curr_edge := edges.get ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self _)⟩
                  let next_edge := edges.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                  curr_edge < next_edge) ∧
                -- The first edge is at or below the minimum data value
                (let min_val := (data.toArray.foldl min (data.get ⟨0, Nat.succ_pos _⟩) : Float)
                 let first_edge := edges.get ⟨0, Nat.succ_pos _⟩
                 first_edge ≤ min_val) ∧
                -- The last edge is at or above the maximum data value
                (let max_val := (data.toArray.foldl max (data.get ⟨0, Nat.succ_pos _⟩) : Float)
                 let last_edge := edges.get ⟨num_bins, Nat.lt_succ_self _⟩
                 last_edge ≥ max_val) ∧
                -- The bins have equal width (equal spacing between consecutive edges)
                (∀ i j : Fin num_bins, 
                  let bin_width_i := edges.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ - 
                                    edges.get ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self _)⟩
                  let bin_width_j := edges.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ - 
                                    edges.get ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self _)⟩
                  bin_width_i = bin_width_j) ∧
                -- All data values fall within the range of the edges
                (let first_edge := edges.get ⟨0, Nat.succ_pos _⟩
                 let last_edge := edges.get ⟨num_bins, Nat.lt_succ_self _⟩
                 ∀ i : Fin (n + 1), 
                   first_edge ≤ data.get i ∧ data.get i ≤ last_edge)⌝⦄ := by
  sorry
-- </vc-theorems>