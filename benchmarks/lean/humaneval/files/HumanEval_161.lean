/- 
function_signature: "def solve(string : String) -> String"
docstring: |
    You are given a string s.
    if s[i] is a letter, reverse its case from lower to upper or vise versa,
    otherwise keep it as it is.
    If the string contains no letters, reverse the string.
    The function should return the resulted string.
test_cases:
  - input: "1234"
    expected_output: "4321"
  - input: "ab"
    expected_output: "AB"
  - input: "#a@C"
    expected_output: "#A@c"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(string : String) :=
-- spec
let spec (result: String) :=
result.length = string.length ∧
let hasNoAlphabet := string.all (λ c => not (c.isAlpha));
(hasNoAlphabet →
  result.toList = string.toList.reverse) ∧
(hasNoAlphabet = false →
  ∀ i, i < string.length →
  let c := string.get! ⟨i⟩;
  (c.isAlpha → ((c.isLower → c.toUpper = result.get! ⟨i⟩) ∨
              (c.isUpper → c.toLower = result.get! ⟨i⟩))) ∧
  (¬ c.isAlpha → c = result.get! ⟨i⟩))
-- program terminates
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

theorem correctness
(s: String)
: problem_spec implementation s :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "1234" = "4321"
-- #test implementation "ab" = "AB"
-- #test implementation "#a@C" = "#A@c"