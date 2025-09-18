-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_comments (source : List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_has_strings {source : List String} :
  ∀ x ∈ remove_comments source, x = x := by sorry

theorem empty_lines_removed {source : List String} :
  (∀ s ∈ source, s = "") →
  remove_comments source = [] := by sorry

theorem only_line_comments_removed {source : List String} :
  (∀ s ∈ source, ∃ rest, s = "//" ++ rest) →
  remove_comments source = [] := by sorry

theorem output_lines_not_empty {source : List String} :
  let result := remove_comments source
  ∀ line ∈ result, line.trim ≠ "" := by sorry
-- </vc-theorems>