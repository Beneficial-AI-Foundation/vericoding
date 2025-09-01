/- 
function_signature: "def reverse_delete(s : str, c : str) -> (str, bool)"
docstring: |
    We are given two strings s and c, you have to deleted all the characters in s that are equal to any character in c
    then check if the result string is palindrome.
    A string is called palindrome if it reads the same backward as forward.
    You should return a tuple containing the result string and True/False for the check.
    -- Note: We assume the deletions preserve the order of the remaining characters.
test_cases:
  - input: ["abcde", "ae"]
    expected_output: ("bcd", False)
  - input: ["abcdef", "b"]
    expected_output: ("acdef", False)
  - input: ["abcdedcba", "ab"]
    expected_output: ('cdedc', True)
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) (c: String) : String × Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String → (String × Bool))
-- inputs
(s: String)
(c: String) :=
-- spec
let spec (result : String × Bool) :=
  let (result_str, result_bool) := result
  result_bool = (List.Palindrome result_str.data) ∧
  (c.data.length = 0 → result_str = s) ∧
  (c.data.length > 0 →
    result_str =
    (implementation
      (String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c])))
      (c.drop 1)).fst)

-- program termination
∃ result,
  implementation s c = result ∧
  spec result

theorem correctness
(s c: String)
: problem_spec implementation s c
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "abcde" "ae" = ("bcd", False)
-- #test implementation "abcdef" "b" = ("acdef", False)
-- #test implementation "abcdedcba" "ab" = ("cdedc", True)