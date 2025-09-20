-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def highest_rank (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem highest_rank_in_input {arr : List Int} (h : arr ≠ []) :
  highest_rank arr ∈ arr :=
sorry

theorem highest_rank_max_frequency {arr : List Int} (h : arr ≠ []) :
  ∀ x ∈ arr, (List.count x arr) ≤ (List.count (highest_rank arr) arr) :=
sorry

theorem highest_rank_max_value {arr : List Int} (h : arr ≠ []) :
  ∀ x ∈ arr, (List.count x arr = List.count (highest_rank arr) arr) → 
  x ≤ highest_rank arr :=
sorry

theorem highest_rank_deterministic {arr : List Int} (h : arr ≠ []) :
  highest_rank arr = highest_rank arr :=
sorry

theorem highest_rank_order_independent {arr : List Int} (h : arr ≠ []) :
  highest_rank arr = highest_rank (List.reverse arr) :=
sorry
-- </vc-theorems>