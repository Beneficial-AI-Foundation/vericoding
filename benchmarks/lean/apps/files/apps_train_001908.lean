-- <vc-helpers>
-- </vc-helpers>

def remove_comments (source : List String) : List String :=
  sorry

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

/-
info: expected1
-/
-- #guard_msgs in
-- #eval remove_comments ["/*Test program */", "int main()", "{ ", "  // variable declaration ", "int a, b, c;", "/* This is a test", "   multiline  ", "   comment for ", "   testing */", "a = b + c;", "}"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval remove_comments ["a/*comment", "line", "more_comment*/b"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval remove_comments ["void func(int k) {", "// this function does nothing /*", "   k = k*2/4;", "   k = k/2;*/", "}"]

-- Apps difficulty: interview
-- Assurance level: unguarded