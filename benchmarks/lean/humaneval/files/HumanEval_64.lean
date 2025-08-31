/- 
function_signature: "def remove_vowels(string: str) -> Nat"
docstring: |
    Write a function vowels_count which takes a string representing
    a word as input and returns the number of vowels in the string.
    Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
    vowel, but only when it is at the end of the given word.
test_cases:
  - input: "abcde"
    expected_output: 2
  - input: "ACEDY"
    expected_output: 3
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isVowel (c : Char) :=
  let vowels := "aeiouAEIOU"
  vowels.contains c
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.data.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
else
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "abcde" = 2
-- #test implementation "ACEDY" = 3