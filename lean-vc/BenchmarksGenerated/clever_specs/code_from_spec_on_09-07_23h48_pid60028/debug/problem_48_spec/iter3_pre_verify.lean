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

-- LLM HELPER
def is_palindrome (s: String) : Bool :=
s.data.reverse = s.data

def implementation (string: String) : Bool := is_palindrome string

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use is_palindrome s
  constructor
  · rfl
  · rfl