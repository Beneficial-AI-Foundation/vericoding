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

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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

theorem correctness
(s: String)
: problem_spec implementation s
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "Hi, my name is John" = ["Hi", "my", "name", "is", "John"]
-- #test implementation "One, two, three, four, five, six" = ["One", "two", "three", "four", "five", "six"]
-- #test implementation "Hi, my name" = ["Hi", "my", "name"]
-- #test implementation "One,, two, three, four, five, six," = ["One", "two", "three", "four", "five", "six"]
-- #test implementation "" = []
-- #test implementation "ahmed     , gamal" = ["ahmed", "gamal"]