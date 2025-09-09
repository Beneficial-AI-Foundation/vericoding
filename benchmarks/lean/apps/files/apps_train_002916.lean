def VALID_LANGUAGES := [
    "czech", "danish", "dutch", "english", "estonian", "finnish", "flemish",
    "french", "german", "irish", "italian", "latvian", "lithuanian",
    "polish", "spanish", "swedish", "welsh"
]

-- <vc-helpers>
-- </vc-helpers>

def greet (language : String) : String :=
  sorry

theorem valid_language_returns_correct_greeting (language : String)
  (h : language ∈ VALID_LANGUAGES) :
  let result := greet language
  (result ≠ "") ∧ 
  (result ≠ "Welcome" ∨ language = "english") :=
sorry

theorem invalid_input_returns_welcome (language : String) 
  (h : language ∉ VALID_LANGUAGES) :
  greet language = "Welcome" :=
sorry

/-
info: 'Welcome'
-/
-- #guard_msgs in
-- #eval greet "english"

/-
info: 'Welkom'
-/
-- #guard_msgs in
-- #eval greet "dutch"

/-
info: 'Welcome'
-/
-- #guard_msgs in
-- #eval greet "IP_ADDRESS_INVALID"

/-
info: 'Welcome'
-/
-- #guard_msgs in
-- #eval greet ""

/-
info: 'Welcome'
-/
-- #guard_msgs in
-- #eval greet 2

-- Apps difficulty: introductory
-- Assurance level: unguarded