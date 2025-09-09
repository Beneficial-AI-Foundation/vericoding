-- <vc-helpers>
-- </vc-helpers>

def highest_rank (arr : List Int) : Int :=
sorry

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

/-
info: 12
-/
-- #guard_msgs in
-- #eval highest_rank [12, 10, 8, 12, 7, 6, 4, 10, 12]

/-
info: 12
-/
-- #guard_msgs in
-- #eval highest_rank [12, 10, 8, 12, 7, 6, 4, 10, 12, 10]

/-
info: 3
-/
-- #guard_msgs in
-- #eval highest_rank [12, 10, 8, 8, 3, 3, 3, 3, 2, 4, 10, 12, 10]

-- Apps difficulty: introductory
-- Assurance level: unguarded