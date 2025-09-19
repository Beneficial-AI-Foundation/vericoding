-- <vc-preamble>
def VALID_LANGUAGES := [
    "czech", "danish", "dutch", "english", "estonian", "finnish", "flemish",
    "french", "german", "irish", "italian", "latvian", "lithuanian",
    "polish", "spanish", "swedish", "welsh"
]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet (language : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>