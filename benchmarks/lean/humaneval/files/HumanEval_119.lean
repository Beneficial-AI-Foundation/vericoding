/- 
function_signature: "def match_parens(l : list[str]) -> str"
docstring: |
    You are given a list of two strings, both strings consist of open
    parentheses '(' or close parentheses ')' only.
    Your job is to check if it is possible to concatenate the two strings in
    some order, that the resulting string will be good.
    A string S is considered to be good if and only if all parentheses in S
    are balanced. For example: the string '(())()' is good, while the string
    '())' is not.
    Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.
test_cases:
  - input: ['()(', ')']
    expected_output: "Yes"
  - input: [')', ')']
    expected_output: "No"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(l: List String) :=
-- spec
let spec (result : String) :=
  l.length = 2 →
  l[0]!.all (fun c => c = '(' ∨ c = ')') →
  l[1]!.all (fun c => c = '(' ∨ c = ')') →
  let res := (balanced_paren_non_computable (l[0]! ++ l[1]!) '(' ')' ∨
            balanced_paren_non_computable (l[1]! ++ l[0]!) '(' ')')
  (res → result = "Yes") ∧
  (¬ res → result = "No")
-- program termination
∃ result,
  implementation l = result ∧
  spec result

theorem correctness
(l: List String)
: problem_spec implementation l
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation ['()(', ')'] = "Yes"
-- #test implementation [')', ')'] = "No"