-- <vc-helpers>
-- </vc-helpers>

def toCamelCase (s : Option String) : String := sorry

theorem to_camel_case_no_separators (parts : List String) (h : parts ≠ []) :
  let joined := " ".intercalate parts
  let result := toCamelCase (some joined)
  ¬ result.contains '_' ∧
  ¬ result.contains '-' ∧
  ¬ result.contains ' ' := sorry

theorem to_camel_case_first_word_preserved 
  (first : String) (sep : Char) (rest : List String)
  (h_sep : sep = '-' ∨ sep = '_') :
  let text := first ++ sep.toString ++ String.join (List.intersperse sep.toString rest)
  let result := toCamelCase (some text)
  result.startsWith first := sorry

theorem to_camel_case_empty_input :
  toCamelCase (some "") = "" ∧ toCamelCase none = "" := sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval to_camel_case ""

/-
info: 'theStealthWarrior'
-/
-- #guard_msgs in
-- #eval to_camel_case "the_stealth_warrior"

/-
info: 'TheStealthWarrior'
-/
-- #guard_msgs in
-- #eval to_camel_case "The-Stealth-Warrior"

-- Apps difficulty: introductory
-- Assurance level: unguarded