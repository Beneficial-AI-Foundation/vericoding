/- 
function_signature: "def encode_cyclic(s: str) -> str"
docstring: |
  Returns an encoded string by cycling each group of three consecutive characters.
  Specifically, each group of exactly three characters 'abc' is transformed to 'bca'.
  Groups of fewer than three characters at the end of the string remain unchanged.
test_cases:
  - input: "abcdef"
    expected_output: "bcaefd"
  - input: "abcde"
    expected_output: "bcade"
  - input: "ab"
    expected_output: "ab"
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
(impl: String → String)
(s: String) :=
let n := s.length;
let extract (chars: List Char) (start_index: ℕ) (end_index: ℕ) :=
  (chars.drop start_index).take (end_index - start_index + 1);
let spec (result: String) :=
  let encoded_chars := result.toList;
  let original_chars := s.toList;
  encoded_chars.length = n ∧
  (∀ i : ℕ, i * 3 + 3 ≤ n →
    extract encoded_chars (i * 3) (i * 3 + 2) =
      [original_chars[i * 3 + 1]!, original_chars[i * 3 + 2]!, original_chars[i * 3]!]) ∧
  (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
    extract original_chars (n - n % 3) (n - 1));
-- program termination
∃ result,
  impl s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "abcdef" = "bcaefd"
-- #test implementation "abcde" = "bcade"
-- #test implementation "ab" = "ab"