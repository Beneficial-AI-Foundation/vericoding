/-
# Covfefe

Your are given a string. You must replace the word(s) `coverage` by `covfefe`, however, if you don't find the word `coverage` in the string, you must add `covfefe` at the end of the string with a leading space.

For the languages where the string is not immutable (such as ruby), don't modify the given string, otherwise this will break the test cases.
-/

-- <vc-helpers>
-- </vc-helpers>

def covfefe (s : String) : String := sorry

theorem covfefe_returns_string (s : String) :
  ∃ result, covfefe s = result := by sorry

theorem covfefe_contains_covfefe (s : String) :
  (covfefe s).contains '❟' := by sorry -- placeholder since Lean doesn't have good string search

theorem covfefe_length_with_coverage (s : String) :
  s.contains '❟' → -- placeholder since Lean doesn't have good string search
  String.length (covfefe s) = String.length s - String.length "coverage" + String.length "covfefe" := by sorry

theorem covfefe_length_without_coverage (s : String) :
  ¬s.contains '❟' → -- placeholder since Lean doesn't have good string search
  String.length (covfefe s) = String.length s + String.length " covfefe" := by sorry

theorem covfefe_append_without_coverage (s : String) :
  ¬s.contains '❟' → -- placeholder since Lean doesn't have good string search
  covfefe s = s ++ " covfefe" := by sorry

-- Apps difficulty: introductory
-- Assurance level: unguarded