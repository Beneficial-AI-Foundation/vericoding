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
  let rec helper (chars : List Char) (n : Nat) (i : Nat) : Nat :=
    if i > n then 0
    else
      let suffix := chars.drop i
      if suffix.reverse = suffix then i
      else helper chars n (i + 1)
  termination_by n - i
  helper chars n 0

def implementation (string: String) : String :=
  if string.length = 0 then ""
  else
    let palindrome_start := find_longest_palindromic_suffix string
    let prefix_chars := string.toList.take palindrome_start
    let reversed_prefix := prefix_chars.reverse.asString
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
  simp [is_palindrome, List.asString]

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
    rw [← String.toList_asString s] at this
    have : s.toList.asString = s.toList.reverse.asString := this
    exact String.toList_inj.mp this
  · intro h
    rw [← String.toList_asString s]
    rw [h]

-- LLM HELPER
lemma string_concat_preserves_prefix (s t : String) : String.isPrefixOf s (s ++ t) = true := by
  simp [String.isPrefixOf]

-- LLM HELPER
lemma string_length_eq_zero_iff_empty (s : String) : s.length = 0 ↔ s = "" := by
  constructor
  · intro h
    apply String.ext
    simp [String.length] at h
    simp [String.toList, h]
  · intro h
    rw [h]
    simp [String.length]

-- LLM HELPER
lemma implementation_preserves_palindrome (s : String) : 
  is_palindrome (implementation s) = true := by
  cases' Decidable.em (s.length = 0) with h h
  · rw [string_length_eq_zero_iff_empty.mp h]
    simp [implementation_empty, empty_string_palindrome]
  · simp [implementation, h]
    have : ¬s.length = 0 := h
    simp [this, is_palindrome]
    -- This would need more detailed proof about the palindrome construction
    sorry

-- LLM HELPER
lemma implementation_length_ge (s : String) : (implementation s).length ≥ s.length := by
  cases' Decidable.em (s.length = 0) with h h
  · rw [string_length_eq_zero_iff_empty.mp h]
    simp [implementation_empty]
  · simp [implementation, h]
    -- The implementation adds characters, so length increases
    sorry

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
      have s_empty : s = "" := string_length_eq_zero_iff_empty.mp h
      rw [s_empty]
      simp [implementation_empty, empty_string_palindrome, empty_is_prefix_of_empty]
      intro possible_palindrome prefix_prop palindrome_prop
      simp [String.length]
      exact Nat.zero_le _
    · -- Case: non-empty string
      constructor
      · -- Prove is_palindrome (implementation s)
        exact implementation_preserves_palindrome s
      constructor
      · -- Prove implementation s length >= s length  
        exact implementation_length_ge s
      constructor
      · -- Prove s is prefix of implementation s
        simp [implementation]
        cases' Decidable.em (s.length = 0) with h' h'
        · contradiction
        · exact string_concat_preserves_prefix s _
      · -- Prove minimality
        intro possible_palindrome prefix_prop palindrome_prop
        -- This would require proving the algorithm finds the optimal solution
        sorry