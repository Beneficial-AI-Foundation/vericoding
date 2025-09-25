-- <vc-preamble>
def max_list (l: List Int) : Int :=
  match l with
  | [] => 0
  | h::t => (List.foldl max h t)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute_table_scores (n: Nat) (first_row: List Int) : List Int := sorry

theorem compute_table_scores_length {n: Nat} {first_row: List Int} :
  List.length (compute_table_scores n first_row) = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compute_table_scores_min_bound {n: Nat} {first_row: List Int} (h: n > 0):
  ∀ x ∈ compute_table_scores n first_row, x ≥ max_list first_row + 1 := sorry

theorem compute_table_scores_max_bound {n: Nat} {first_row: List Int} (h: n > 0):
  ∀ x ∈ compute_table_scores n first_row, x ≤ max_list first_row + n := sorry

theorem compute_table_scores_min_element {n: Nat} {first_row: List Int} (h: n > 0):
  List.foldl min (max_list first_row + n) (compute_table_scores n first_row) ≥ max_list first_row + 1 := sorry

theorem compute_table_scores_max_element {n: Nat} {first_row: List Int} (h: n > 0):
  List.foldl max 0 (compute_table_scores n first_row) ≤ max_list first_row + n := sorry
-- </vc-theorems>