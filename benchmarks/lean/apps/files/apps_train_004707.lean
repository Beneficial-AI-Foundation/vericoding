/-
I will give you two strings. I want you to transform stringOne into stringTwo one letter at a time.

Example:
-/

-- <vc-helpers>
-- </vc-helpers>

def mutateMyStrings (s1 s2 : String) : String := sorry

theorem mutate_identical_strings (s : String) (h : s.length > 0) : 
  mutateMyStrings s s = s ++ "\n" := sorry

/-
  Implicit assumptions about string:
  - Non-empty
  - Contains only printable ASCII characters (codepoints 32-126)
  - Length ≤ 20
-/

-- Apps difficulty: introductory
-- Assurance level: unguarded