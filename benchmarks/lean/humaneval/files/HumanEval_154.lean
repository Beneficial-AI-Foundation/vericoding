/- 
function_signature: "def cycpattern_check(String a, String b) -> Bool"
docstring: |
    You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word, else False
test_cases:
  - input: ["abcd", "abd"]
    expected_output: False
  - input: ["hello", "ell"]
    expected_output: True
  - input: ["whassup", "psus"]
    expected_output: False
  - input: ["abab", "baa"]
    expected_output: True
  - input: ["efef", "eeff"]
    expected_output: False
  - input: ["himenss", "simen"]
    expected_output: True
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.containsSubstr b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

theorem correctness
(a b: String)
: problem_spec implementation a b :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "abcd" "abd" = False
-- #test implementation "hello" "ell" = True
-- #test implementation "whassup" "psus" = False
-- #test implementation "abab" "baa" = True
-- #test implementation "efef" "eeff" = False
-- #test implementation "himenss" "simen" = True