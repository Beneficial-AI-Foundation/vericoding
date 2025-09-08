/- 
function_signature: "def make_palindrome(string: str) -> str"
docstring: |
    Find the shortest palindrome that begins with a supplied string.
    Algorithm idea is simple:
    - Find the longest postfix of supplied string that is a palindrome.
    - Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
test_cases:
  - input: ""
    expected_output: ""
  - input: "cat"
    expected_output: "catac"
  - input: "cata"
    expected_output: "catac"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: is_palindrome
use: |
  Helper to check if a string is a palindrome.
problems:
  - 10
  - 48
-/
def is_palindrome
(s: String): Bool :=
s = s.toList.reverse.asString

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def find_longest_palindromic_suffix (s: String) : Nat :=
  let chars := s.toList
  let n := chars.length
  let rec helper (i : Nat) : Nat :=
    if i > n then 0
    else
      let suffix := chars.drop i
      if suffix.reverse = suffix then i
      else helper (i + 1)
  helper 0

def implementation (string: String) : String :=
  if string.length = 0 then ""
  else
    let palindrome_start := find_longest_palindromic_suffix string
    let prefix_to_reverse := string.toSubstring 0 palindrome_start
    let reversed_prefix := prefix_to_reverse.toString.toList.reverse.asString
    string ++ reversed_prefix

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
is_palindrome result ∧
result.length ≥ string.length ∧
string.isPrefixOf result ∧
-- comprehensive check that the result is the shortest palindrome
(∀ (possible_palindrome: String),
string.isPrefixOf possible_palindrome →
is_palindrome possible_palindrome →
result.length ≤ possible_palindrome.length);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma empty_string_palindrome : is_palindrome "" = true := by
  simp [is_palindrome]

-- LLM HELPER
lemma implementation_empty : implementation "" = "" := by
  simp [implementation]

-- LLM HELPER
lemma empty_is_prefix_of_empty : String.isPrefixOf "" "" = true := by
  simp [String.isPrefixOf]

-- LLM HELPER
lemma palindrome_property (s : String) : is_palindrome s = true ↔ s.toList = s.toList.reverse := by
  simp [is_palindrome]
  constructor
  · intro h
    have : s = s.toList.reverse.asString := h
    rw [← List.asString_toList s] at this
    have : s.toList.asString = s.toList.reverse.asString := this
    exact List.asString_inj.mp this
  · intro h
    rw [← List.asString_toList s]
    rw [h]

-- LLM HELPER
lemma string_concat_preserves_prefix (s t : String) : String.isPrefixOf s (s ++ t) = true := by
  simp [String.isPrefixOf, String.append]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · by_cases h : s.length = 0
    · -- Case: empty string
      have s_empty : s = "" := by
        apply String.ext
        simp [String.toList, h]
      rw [s_empty]
      simp [implementation_empty, empty_string_palindrome, empty_is_prefix_of_empty]
      intro possible_palindrome prefix_prop palindrome_prop
      simp [String.isPrefixOf] at prefix_prop
      simp [String.length]
      exact Nat.zero_le _
    · -- Case: non-empty string
      constructor
      · -- Prove is_palindrome (implementation s)
        sorry
      constructor
      · -- Prove implementation s length >= s length  
        simp [implementation]
        split_ifs with h'
        · contradiction
        · simp [String.length]
          sorry
      constructor
      · -- Prove s is prefix of implementation s
        simp [implementation]
        split_ifs with h'
        · contradiction  
        · exact string_concat_preserves_prefix s _
      · -- Prove minimality
        intro possible_palindrome prefix_prop palindrome_prop
        sorry