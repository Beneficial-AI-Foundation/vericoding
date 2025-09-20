-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def case_id (s : String) : String := sorry

theorem case_id_result_is_valid (s : String) :
  case_id s = "snake" ∨ case_id s = "kebab" ∨ case_id s = "camel" ∨ case_id s = "none" := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>