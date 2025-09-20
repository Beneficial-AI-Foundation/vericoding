-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.substringExists (s : String) (sub : String) : Bool :=
sorry

def alan_annoying_kid (phrase : String) : String :=
sorry

def String.getWords (s : String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alan_preserves_verb (phrase : String) (verb : String)
  (h₁ : phrase.startsWith "Today I")
  (h₂ : verb ∈ phrase.getWords) :
  verb ∈ (alan_annoying_kid phrase).getWords :=
sorry

theorem alan_response_structure (phrase : String) (h₁ : phrase.startsWith "Today I") :
  let response := alan_annoying_kid phrase
  response.startsWith "I don't think you" ∧
  response.endsWith "!" ∧
  response.substringExists "today" :=
sorry

theorem alan_response_negation_negative (phrase : String) (h₁ : phrase.startsWith "Today I didn't") :
  let response := alan_annoying_kid phrase
  response.substringExists "I think you did" ∧
  response.substringExists "it!" :=
sorry

theorem alan_response_negation_positive (phrase : String)
  (h₁ : phrase.startsWith "Today I")
  (h₂ : ¬phrase.substringExists "didn't") :
  let response := alan_annoying_kid phrase
  response.substringExists "I think you didn't" ∧
  response.substringExists "at all!" :=
sorry
-- </vc-theorems>