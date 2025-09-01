/- 
function_signature: "def odd_count(lst : list[str]) -> list[str]"
docstring: |
    Given a list of strings, where each string consists of only digits, return a list.
    Each element i of the output should be "the number of odd elements in the
    string i of the input." where all the i's should be replaced by the number
    of odd digits in the i'th string of the input.
    Note(George): Found it hard to not leak the implementation, so I opted for a recursive statement.
test_cases:
  - input: ['1234567']
    expected_output: ["the number of odd elements 4n the str4ng 4 of the 4nput."]
  - input: ['3',"11111111"]
    expected_output: ["the number of odd elements 1n the str1ng 1 of the 1nput.",
     "the number of odd elements 8n the str8ng 8 of the 8nput."]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List String) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result : List String) :=
  lst.all (fun s => s.data.all (fun c => c.isDigit)) →
  (result.length = 0 ↔ lst.length = 0) ∧
  (result.length > 0 →
  let num_odd_digits := (lst.head!.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
  result.head! = "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
  ∧ result.tail! = implementation lst.tail!)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List String)
: problem_spec implementation lst
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation ['1234567'] = ["the number of odd elements 4n the str4ng 4 of the 4nput."]
-- #test implementation ['3',"11111111"] = ["the number of odd elements 1n the str1ng 1 of the 1nput.",
--  "the number of odd elements 8n the str8ng 8 of the 8nput."]