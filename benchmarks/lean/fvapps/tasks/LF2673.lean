-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (words : List String) : List Nat := sorry

theorem solve_output_matches_input_length 
  (words : List String) (h : words ≠ []) : 
  List.length (solve words) = List.length words := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_counts_in_valid_range
  (words : List String) (h : words ≠ []) :
  ∀ i, i < List.length (solve words) →
    (0 ≤ (solve words).get! i ∧ 
     (solve words).get! i ≤ String.length (words.get! i)) := sorry

theorem solve_case_insensitive
  (words : List String) (h : words ≠ []) :
  solve words = solve (List.map String.toUpper words) ∧
  solve words = solve (List.map String.toLower words) := sorry
-- </vc-theorems>