-- LLM HELPER
def is_palindrome (s: String) : Bool :=
  s.data.reverse = s.data

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
result ↔ is_palindrome string
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : Bool := 
  is_palindrome string

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  unfold implementation
  use is_palindrome s
  constructor
  · rfl
  · constructor
    · intro h
      exact h
    · intro h
      exact h