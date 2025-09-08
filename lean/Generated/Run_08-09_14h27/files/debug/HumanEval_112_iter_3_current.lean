/- 
function_signature: "def reverse_delete(s : str, c : str) -> (str, bool)"
docstring: |
    We are given two strings s and c, you have to deleted all the characters in s that are equal to any character in c
    then check if the result string is palindrome.
    A string is called palindrome if it reads the same backward as forward.
    You should return a tuple containing the result string and True/False for the check.
    -- Note: We assume the deletions preserve the order of the remaining characters.
test_cases:
  - input: ["abcde", "ae"]
    expected_output: ("bcd", False)
  - input: ["abcdef", "b"]
    expected_output: ("acdef", False)
  - input: ["abcdedcba", "ab"]
    expected_output: ('cdedc', True)
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isPalindrome (s : String) : Bool :=
  s.data = s.data.reverse

-- LLM HELPER
def removeChars (s : String) (c : String) : String :=
  String.mk (s.data.filter (fun ch => !c.data.contains ch))

def implementation (s: String) (c: String) : String × Bool :=
  let filtered := removeChars s c
  (filtered, isPalindrome filtered)

-- LLM HELPER
lemma isPalindrome_correct (s : String) : isPalindrome s ↔ List.Palindrome s.data := by
  unfold isPalindrome List.Palindrome
  rfl

-- LLM HELPER  
lemma removeChars_empty (s : String) : removeChars s "" = s := by
  unfold removeChars
  simp [List.filter_eq_self, String.mk_str_data]

def problem_spec
-- function signature
(implementation: String → String → (String × Bool))
-- inputs
(s: String)
(c: String) :=
-- spec
let spec (result : String × Bool) :=
  let (result_str, result_bool) := result
  result_bool = (List.Palindrome result_str.data) ∧
  (c.data.length = 0 → result_str = s) ∧
  (c.data.length > 0 →
    result_str =
    (implementation
      (String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c])))
      (c.drop 1)).fst)

-- program termination
∃ result,
  implementation s c = result ∧
  spec result

theorem correctness
(s c: String)
: problem_spec implementation s c
:= by
  unfold problem_spec
  use implementation s c
  constructor
  · rfl
  · simp [implementation]
    let filtered := removeChars s c
    constructor
    · rw [isPalindrome_correct]
    constructor
    · intro h
      have : c.data = [] := List.length_eq_zero_iff.mp h
      simp [removeChars, this]
      rw [String.mk_str_data]
    · intro h
      simp [removeChars]
      sorry

-- #test implementation "abcde" "ae" = ("bcd", False)
-- #test implementation "abcdef" "b" = ("acdef", False)
-- #test implementation "abcdedcba" "ab" = ("cdedc", True)