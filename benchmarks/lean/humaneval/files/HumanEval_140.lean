/- 
function_signature: "def fix_spaces(text: str) -> str"
docstring: |
    Given a string text, replace all spaces in it with underscores,
    and if a string has more than 2 consecutive spaces,
    then replace all consecutive spaces with -
test_cases:
  - input: "Example"
    expected_output: "Example"
  - input: "Example 1"
    expected_output: "Example_1"
  - input: " Example 2"
    expected_output: "_Example_2"
  - input: " Example   3"
    expected_output: "_Example-3"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (text: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(text: String) :=
-- spec
let spec (result: String) :=
  (result = "" → text = "") ∧
  (result ≠ "" → (
    (∃ pref s, text = pref ++ s
      ∧ pref.length = 1
      ∧ pref ≠ " "
      ∧ result = pref ++ impl s)
    ∨
    (∃ pref s : String, text = pref ++ s ∧ pref ≠ "" ∧ (∀ ch, ch ∈ pref.toList → ch = ' ')
      ∧ let k := pref.length;
        (k ≤ 2 → result = (String.replicate k '_') ++ (impl (text.drop k)))
      ∧ (2 < k → result = "-" ++ (impl (text.drop k)))) )
  )
-- program termination
∃ result, impl text = result ∧
-- return value satisfies spec
spec result

theorem correctness
(text: String)
: problem_spec implementation text :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "Example" = "Example"
-- #test implementation "Example 1" = "Example_1"
-- #test implementation " Example 2" = "_Example_2"
-- #test implementation " Example   3" = "_Example-3"