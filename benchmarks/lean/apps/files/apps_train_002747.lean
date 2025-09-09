-- <vc-helpers>
-- </vc-helpers>

def find (s : String) : String := sorry

theorem single_char_strings (s : String) 
  (h : ∀ c ∈ s.data, c = '!') :
  find s = "" := sorry

theorem no_exclaim_question (s : String)
  (h : ∀ c ∈ s.data, c ≠ '!' ∧ c ≠ '?') :
  find s = "" := sorry

theorem result_only_valid_chars (s : String) :
  ∀ c ∈ (find s).data, c = '!' ∨ c = '?' := sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval find "!!"

/-
info: '!??'
-/
-- #guard_msgs in
-- #eval find "!??"

/-
info: '!!???'
-/
-- #guard_msgs in
-- #eval find "!!???!????"

-- Apps difficulty: introductory
-- Assurance level: unguarded