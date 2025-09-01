/- 
function_signature: "def words_in_sentence(sentence: str) -> str"
docstring: |
    You are given a string representing a sentence,
    the sentence contains some words separated by a space,
    and you have to return a string that contains the words from the original sentence,
    whose lengths are prime numbers,
    the order of the words in the new string should be the same as the original one.

    Constraints:
    * 1 <= len(sentence) <= 100
    * sentence contains only letters
test_cases:
  - input: "This is a test"
    expected_output: "is"
  - input: "lets go for swimming"
    expected_output: "go for"
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (sentence : String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(sentence: String) :=
-- spec
let spec (result: String) :=
let words := sentence.splitOn;
let result_words := result.splitOn;
  1 ≤ sentence.length → sentence.length ≤ 100 →
  sentence.all (fun x => Char.isAlpha x) →
  result_words.length ≤ words.length ∧
  (∀ word ∈ result_words, word ∈ words ∧ Nat.Prime word.length) ∧
  match result_words with
  | [] => ∀ word ∈ words, ¬(Nat.Prime word.length)
  | head :: tail => if Nat.Prime head.length ∧ head = words[0]! then String.join tail = impl (String.join (words.drop 1))
    else result = impl (String.join (words.drop 1))
-- program termination
∃ result, impl sentence = result ∧
-- return value satisfies spec
spec result

theorem correctness
(sentence : String)
: problem_spec implementation sentence :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "This is a test" = "is"
-- #test implementation "lets go for swimming" = "go for"