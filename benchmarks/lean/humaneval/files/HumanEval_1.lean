/- 
function_signature: "def separate_paren_groups(paren_string: str) -> List[str]"
docstring: |
    Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
    separate those group into separate strings and return the list of those.
    Separate groups are balanced (each open brace is properly closed) and not nested within each other
    Ignore any spaces in the input string.
test_cases:
  - input: "( ) (( )) (( )( ))"
    expected_output:
      - "()"
      - "(())"
      - "(()())"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (paren_string: String) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → List String)
-- inputs
(paren_string: String) :=
-- spec
let paren_string_filtered := (paren_string.toList.filter (fun c => c == '(' ∨  c == ')')).asString;
let spec (result_list: List String) :=
-- concat of result is input_filtered
(result_list.foldl (· ++ ·) "" = paren_string_filtered) ∧
-- each item in result is balanced and has only one group
(∀ str ∈ result_list, balanced_paren_non_computable str '(' ')' ∧ count_paren_groups str = 1);
-- program terminates
∃ result, impl paren_string = result ∧
-- return value satisfies spec
spec result

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string :=
-- <vc-proof>
  sorry
-- </vc-proof>

#test implementation "( ) (( )) (( )( ))" = ["()", "(())", "(()())"]