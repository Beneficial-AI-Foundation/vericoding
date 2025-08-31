/- 
function_signature: "def check_if_last_char_is_a_letter(txt: str) -> Bool"
docstring: |
    Create a function that returns True if the last character
    of a given string is an alphabetical character and is not
    a part of a word, and False otherwise.
    Note: "word" is a group of characters separated by space.
test_cases:
  - input: "apple pie"
    expected_output: False
  - input: "apple pi e"
    expected_output: True
  - input: "apple pi e "
    expected_output: False
  - input: ""
    expected_output: False
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (txt: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(txt: String) :=
-- spec
let spec (result: Bool) :=
  let words := txt.splitOn " ";
  match words with
  | [] => result = False
  | [last_word] => (result ↔ last_word.length = 1 ∧ (let diff := (last_word.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25))
  | head::tail => result ↔ (let tail_txt := String.join tail; impl tail_txt);
-- program terminates
∃ result, impl txt = result ∧
-- return value satisfies spec
spec result

theorem correctness
(txt: String)
: problem_spec implementation txt :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "apple pie" = false
-- #test implementation "apple pi e" = true
-- #test implementation "apple pi e " = false
-- #test implementation "" = false