-- <vc-helpers>
-- </vc-helpers>

def generate_hashtag (s : String) : Option String := sorry

theorem generate_hashtag_basic_cases :
  generate_hashtag "hello world" = some "#HelloWorld" ∧
  generate_hashtag "   hello     world   " = some "#HelloWorld" ∧
  generate_hashtag "" = none := sorry

theorem generate_hashtag_length_cases {n : Nat} :
  (n = 138 → generate_hashtag (String.mk (List.replicate n 'a')) = some ("#A" ++ String.mk (List.replicate 137 'a'))) ∧
  (n = 140 → generate_hashtag (String.mk (List.replicate n 'a')) = none) := sorry

theorem generate_hashtag_capitalization :
  generate_hashtag "hello World" = some "#HelloWorld" ∧
  generate_hashtag "HELLO WORLD" = some "#HelloWorld" ∧
  generate_hashtag "hELLo wORLd" = some "#HelloWorld" := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval generate_hashtag ""

/-
info: '#HelloWorld'
-/
-- #guard_msgs in
-- #eval generate_hashtag "hello world"

/-
info: '#HelloWorld'
-/
-- #guard_msgs in
-- #eval generate_hashtag "   hello     world   "

/-
info: False
-/
-- #guard_msgs in
-- #eval generate_hashtag "x" * 140

-- Apps difficulty: introductory
-- Assurance level: unguarded