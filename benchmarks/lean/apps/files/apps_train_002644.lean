-- <vc-helpers>
-- </vc-helpers>

def solve : String → String := sorry

theorem solve_basic_cases₁ :
  solve "3(a)" = "aaa" := sorry

theorem solve_basic_cases₂ :
  solve "2(ab)" = "abab" := sorry

theorem solve_nested_cases₁ :
  solve "2(a2(b))" = "abbabb" := sorry

theorem solve_nested_cases₂ :
  solve "3(a2(bc))" = "abcbcabcbcabcbc" := sorry

theorem solve_letters_only :
  solve "abc" = "abc" := sorry

theorem solve_with_leading_letters₁ :
  solve "k2(a)" = "kaa" := sorry

theorem solve_with_leading_letters₂ :
  solve "a2(b)" = "abb" := sorry

/-
info: 'ababab'
-/
-- #guard_msgs in
-- #eval solve "3(ab)"

/-
info: 'abbbabbb'
-/
-- #guard_msgs in
-- #eval solve "2(a3(b))"

/-
info: 'kabaccbaccbacc'
-/
-- #guard_msgs in
-- #eval solve "k(a3(b(a2(c))))"

-- Apps difficulty: introductory
-- Assurance level: unguarded