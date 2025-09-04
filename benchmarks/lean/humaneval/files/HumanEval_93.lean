/- 
function_signature: "def encode(s : str) -> str"
docstring: |
    Write a function that takes a message, and encodes in such a
    way that it swaps case of all letters, replaces all vowels in
    the message with the letter that appears 2 places ahead of that
    vowel in the english alphabet.
    Assume only letters.
test_cases:
  - input: "test"
    expected_output: "TGST"
  - input: "This is a message"
    expected_output: "tHKS KS C MGSSCGG"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (λ c => c.isAlpha) →
  result.length = s.length ∧
  (∀ i, i < s.length →
    let c := s.data[i]!;
    let c' := result.data[i]!;
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
      c.isUpper → c'.val = c.toLower.val + 2 ∧
      c.isLower → c'.val = c.toUpper.val + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "test" = "TGST"
-- #test implementation "This is a message" = "tHKS KS C MGSSCGG"