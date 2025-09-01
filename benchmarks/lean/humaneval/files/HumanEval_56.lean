/- 
function_signature: "def correct_bracketing(brackets: str) -> Bool"
docstring: |
    brackets is a string of "<" and ">".
    return True if every opening bracket has a corresponding closing bracket, i.e., (each open bracket is properly closed)
test_cases:
  - input: "<"
    expected_output: False
  - input: "<>"
    expected_output: True
  - input: "<<><>>"
    expected_output: True
  - input: "><<>"
    expected_output: False
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (brackets: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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

theorem correctness
(brackets: String)
: problem_spec implementation brackets :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "<" = false
-- #test implementation "<>" = true
-- #test implementation "<<><>>" = true
-- #test implementation "><<>" = false