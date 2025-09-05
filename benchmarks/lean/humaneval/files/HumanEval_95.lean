/- 
function_signature: "def check_dict_case(s : dict[str, str]) -> bool"
docstring: |
    Given a dictionary, return True if all keys are strings in lower
    case or all keys are strings in upper case, else return False.
    The function should return False is the given dictionary is empty.
    Note(George): Modified the problem to use strings only for both keys and values.
test_cases:
  - input: {"a":"apple", "b":"banana"}
    expected_output: True
  - input: {"a":"apple", "A":"banana", "B":"banana"}
    expected_output: False
  - input: {"a":"apple", "b":"banana", "a":"apple"}
    expected_output: False
  - input: {"Name":"John", "Age":"36", "City":"Houston"}
    expected_output: False
  - input: {"STATE":"NC", "ZIP":"12345" }
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (D: Std.HashMap String String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Std.HashMap String String → Bool)
-- inputs
(D: Std.HashMap String String) :=
-- spec
let spec (result : Bool) :=
  match D.isEmpty with
  | true => result = false
  | false =>
    let keys := D.keys
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    result = true ↔ all_lower || all_upper
-- program termination
∃ result,
  implementation D = result ∧
  spec result

theorem correctness
(D: Std.HashMap String String)
: problem_spec implementation D
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation (Std.HashMap.ofList [("a", "apple"), ("b", "banana")]) = true
-- #test implementation (Std.HashMap.ofList [("a", "apple"), ("A", "banana"), ("B", "banana")]) = false
-- #test implementation (Std.HashMap.ofList [("a", "apple"), ("b", "banana"), ("a", "apple")]) = false
-- #test implementation (Std.HashMap.ofList [("Name", "John"), ("Age", "36"), ("City", "Houston")]) = false
-- #test implementation (Std.HashMap.ofList [("STATE", "NC"), ("ZIP", "12345")]) = true