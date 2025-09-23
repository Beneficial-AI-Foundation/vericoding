-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def histogramdd {n : Nat} (sample : Vector (Float × Float) n) (bins_x bins_y : Nat) : 
    Id (Vector (Vector Float bins_x) bins_y × Vector Float (bins_x + 1) × Vector Float (bins_y + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem histogramdd_spec {n : Nat} (sample : Vector (Float × Float) n) (bins_x bins_y : Nat) 
    (h_bins_x_pos : bins_x > 0) (h_bins_y_pos : bins_y > 0) :
    ⦃⌜bins_x > 0 ∧ bins_y > 0⌝⦄
    histogramdd sample bins_x bins_y
    ⦃⇓result => 
      let (hist, edges_x, edges_y) := result
      ⌜-- The histogram has the correct dimensions
      (hist.toArray.size = bins_y) ∧
      (∀ i : Fin bins_y, (hist.get i).toArray.size = bins_x) ∧
      -- The edges have the correct sizes
      (edges_x.toArray.size = bins_x + 1) ∧
      (edges_y.toArray.size = bins_y + 1) ∧
      -- The edges are monotonically increasing
      (∀ i : Fin bins_x, edges_x.get ⟨i.val, by omega⟩ < edges_x.get ⟨i.val + 1, by omega⟩) ∧
      (∀ i : Fin bins_y, edges_y.get ⟨i.val, by omega⟩ < edges_y.get ⟨i.val + 1, by omega⟩) ∧
      -- The histogram counts are non-negative
      (∀ i : Fin bins_y, ∀ j : Fin bins_x, (hist.get i).get j ≥ 0) ∧
      -- Each sample point falls into exactly one bin
      (∀ p : Float × Float, p ∈ sample.toArray →
        ∃ i : Fin bins_y, ∃ j : Fin bins_x,
          edges_y.get ⟨i.val, by omega⟩ ≤ p.snd ∧ p.snd < edges_y.get ⟨i.val + 1, by omega⟩ ∧
          edges_x.get ⟨j.val, by omega⟩ ≤ p.fst ∧ p.fst < edges_x.get ⟨j.val + 1, by omega⟩)⌝⦄ := by
  sorry
-- </vc-theorems>