/- 
function_signature: "def is_nested(string: str) -> Bool"
docstring: |
    Create a function that takes a string as input which contains only parentheses.
    The function should return True if and only if there is a valid subsequence of parentheses
    where at least one parenthesis in the subsequence is nested.
test_cases:
  - input: '(())'
    expected_output: True
  - input: '()))))))((((()'
    expected_output: False
  - input: '()()'
    expected_output: False
  - input: '()'
    expected_output: False
  - input: '(()())'
    expected_output: True
  - input: '(())(('
    expected_output: True
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
string.toList.all (fun x => x = '(' ∨ x = ')') →
result = true ↔
  ∃ x : String,
    is_subsequence x.toList string.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x
-- program termination
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

theorem correctness
(string: String)
: problem_spec implementation string :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "(())" = true
-- #test implementation "()))))))((((()" = false
-- #test implementation "()()" = false
-- #test implementation "()" = false
-- #test implementation "(()())" = true
-- #test implementation "(())((" = true