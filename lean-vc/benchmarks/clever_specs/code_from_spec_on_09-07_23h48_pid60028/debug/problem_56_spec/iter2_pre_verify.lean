def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(brackets: String) :=
-- spec
let spec (result: Bool) :=
  brackets.data.all (fun c => c = '<' ∨ c = '>') →
  (result ↔ balanced_paren_non_computable brackets '<' '>')
-- program terminates
∃ result, impl brackets = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open_char close_char : Char) : Bool :=
  let chars := s.data
  let rec check_balance (chars : List Char) (depth : Int) : Bool :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        check_balance rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          check_balance rest (depth - 1)
        else
          false
      else
        check_balance rest depth
  check_balance chars 0

def implementation (brackets: String) : Bool := 
  balanced_paren_non_computable brackets '<' '>'

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  simp [problem_spec]
  use balanced_paren_non_computable brackets '<' '>'
  constructor
  · simp [implementation]
  · simp [balanced_paren_non_computable]
    intro h
    rfl