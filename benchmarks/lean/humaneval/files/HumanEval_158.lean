/- 
function_signature: "def find_max(words: List String) -> String"
docstring: |
    Write a function that accepts a list of strings.
    The list contains different words. Return the word with maximum number
    of unique characters. If multiple strings have maximum number of unique
    characters, return the one which comes first in lexicographical order.
test_cases:
  - input: ["name", "of", "string"]
    expected_output: "string"
  - input: ["name", "enam", "game"]
    expected_output: "enam"
  - input: ["aaaaaaa", "bb", "cc"]
    expected_output: "aaaaaaa"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (words: List String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List String → String)
-- inputs
(words: List String) :=
let unique_chars (string: String) :=
  let string_idx := {i: Nat | i < string.length}.toFinset;
  let characters := string_idx.image (fun i => string.toList[i]!);
  characters.card;
-- spec
let spec (result: String) :=
(result = "" ↔ words.length = 0) ∧
(words.length != 0 → result ∈ words ∧
let unique_chars_list := words.map unique_chars;
let max_unique_chars := unique_chars_list.max?.get!;
unique_chars result = max_unique_chars ∧
∀ i : Nat, i < words.length →
  unique_chars_list[i]! = max_unique_chars →
  result ≤ words[i]!);
-- program terminates
∃ result, impl words = result ∧
-- return value satisfies spec
spec result

theorem correctness
(words: List String)
: problem_spec implementation words :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation ["name", "of", "string"]= "string"
-- #test implementation ["name", "enam", "game"] = "enam"
-- #test implementation ["aaaaaaa", "bb" ,"cc"] = "aaaaaaa"