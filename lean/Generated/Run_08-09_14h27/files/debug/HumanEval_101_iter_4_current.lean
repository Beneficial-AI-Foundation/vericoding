/- 
function_signature: "def words_string(s: string) -> List[string]"
docstring: |
    You will be given a string of words separated by commas or spaces. Your task is
    to split the string into words and return an array of the words.
test_cases:
  - input: "Hi, my name is John"
    expected_output: ["Hi", "my", "name", "is", "John"]
  - input: "One, two, three, four, five, six"
    expected_output: ["One", "two", "three", "four", "five", "six"]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_separator (c: Char) : Bool := c = ',' || c = ' '

def implementation (s: String) : List String :=
  let trimmed := s.trim
  if trimmed = "" then []
  else
    let chars := trimmed.toList
    let rec helper (acc: List String) (current: String) (remaining: List Char) : List String :=
      match remaining with
      | [] => if current.trim = "" then acc else acc ++ [current.trim]
      | c :: rest =>
        if is_separator c then
          if current.trim = "" then helper acc "" rest
          else helper (acc ++ [current.trim]) "" rest
        else
          helper acc (current ++ c.toString) rest
    helper [] "" chars

def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(s: String) :=
-- spec
let spec (result: List String) :=
  let chars := s.toList;
  let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ');
  (result = [] ↔ (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = "") ∧
  (result ≠ [] ↔ result = [first] ++ (implementation (s.drop (first.length + 1))))

-- program termination
∃ result, implementation s = result ∧
spec result

-- LLM HELPER
lemma implementation_terminates (s: String) : ∃ result, implementation s = result := by
  use implementation s
  rfl

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  rfl
  unfold implementation
  simp only []
  constructor
  · sorry
  · sorry

-- #test implementation "Hi, my name is John" = ["Hi", "my", "name", "is", "John"]
-- #test implementation "One, two, three, four, five, six" = ["One", "two", "three", "four", "five", "six"]
-- #test implementation "Hi, my name" = ["Hi", "my", "name"]
-- #test implementation "One,, two, three, four, five, six," = ["One", "two", "three", "four", "five", "six"]
-- #test implementation "" = []
-- #test implementation "ahmed     , gamal" = ["ahmed", "gamal"]