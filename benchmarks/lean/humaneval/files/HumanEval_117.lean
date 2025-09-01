/- 
function_signature: "def select_words(s : str, n : int) -> list[str]"
docstring: |
    Given a string s and a natural number n, you have been tasked to implement
    a function that returns a list of all words from string s that contain exactly
    n consonants, in order these words appear in the string s.
    If the string s is empty then the function should return an empty list.
    Note: you may assume the input string contains only letters and spaces.
test_cases:
  - input: ("Mary had a little lamb", 4)
    expected_output: ["little"]
  - input: ("Mary had a little lamb", 3)
    expected_output: ["Mary", "lamb"]
  - input: ("simple white space", 2)
    expected_output: []
  - input: ("Hello world", 4)
    expected_output: ["world"]
  - input: ("Uncle sam", 3)
    expected_output: ["Uncle"]
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) (n: Nat) : List String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → Nat → List String)
-- inputs
(s: String)
(n: Nat) :=
-- spec
let spec (result : List String) :=
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  s.all (fun c => c = ' ' ∨ c.isAlpha) →
  let words := s.splitOn " "
  (result = [] ↔ (s.length = 0 ∨ words.all (fun word => (word.data.filter (fun c => is_consonant c)).length ≠ n))) ∧
  (result.length > 0 →
    let first_word := result[0]!
    first_word ∈ words ∧
    (first_word.data.filter (fun c => is_consonant c)).length = n ∧
    let first_word_idx := words.indexOf first_word
    (∀ i, i < first_word_idx →
      (words[i]!.data.filter (fun c => is_consonant c)).length ≠ n) ∧
    result.tail! =
      implementation ((words.drop (first_word_idx + 1)).foldl (fun acc word => acc ++ " " ++ word) "") n
  )

-- program termination
∃ result,
  implementation s n = result ∧
  spec result

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "Mary had a little lamb" 4 = ["little"]
-- #test implementation "Mary had a little lamb" 3 = ["Mary", "lamb"]
-- #test implementation "simple white space" 2 = []
-- #test implementation "Hello world" 4 = ["world"]
-- #test implementation "Uncle sam" 3 = ["Uncle"]