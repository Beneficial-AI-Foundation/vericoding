-- <vc-helpers>
-- </vc-helpers>

def case_id (s : String) : String := sorry

theorem case_id_result_is_valid (s : String) :
  case_id s = "snake" ∨ case_id s = "kebab" ∨ case_id s = "camel" ∨ case_id s = "none" := sorry

theorem empty_string_is_none :
  case_id "" = "none" := sorry

theorem single_word_is_none (w : String) :
  w.all (fun c => c.isLower) →
  case_id w = "none" := sorry

theorem snake_case_recognition {words : List String} {joined : String} :
  words.length ≥ 2 →
  (∀ w ∈ words, w ≠ "") →
  (∀ w ∈ words, w.all (fun c => c.isLower)) →
  joined = String.intercalate "_" words →
  case_id joined = "snake" := sorry

theorem basic_kebab_case :
  case_id "hello-world" = "kebab" := sorry

theorem basic_camel_case :
  case_id "helloWorld" = "camel" := sorry

/-
info: 'snake'
-/
-- #guard_msgs in
-- #eval case_id "hello_world"

/-
info: 'snake'
-/
-- #guard_msgs in
-- #eval case_id "hello_to_the_world"

/-
info: 'kebab'
-/
-- #guard_msgs in
-- #eval case_id "hello-world"

/-
info: 'kebab'
-/
-- #guard_msgs in
-- #eval case_id "hello-to-the-world"

/-
info: 'camel'
-/
-- #guard_msgs in
-- #eval case_id "helloWorld"

/-
info: 'camel'
-/
-- #guard_msgs in
-- #eval case_id "helloToTheWorld"

/-
info: 'none'
-/
-- #guard_msgs in
-- #eval case_id "hello_World"

/-
info: 'none'
-/
-- #guard_msgs in
-- #eval case_id "hello-World"

/-
info: 'none'
-/
-- #guard_msgs in
-- #eval case_id "helloworld"

-- Apps difficulty: introductory
-- Assurance level: unguarded