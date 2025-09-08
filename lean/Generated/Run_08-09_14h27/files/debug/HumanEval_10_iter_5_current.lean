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
  (List.range (n + 1)).foldl (fun acc i =>
    let suffix := chars.drop i
    if is_palindrome suffix.asString then max acc (suffix.length) else acc
  ) 0

def implementation (string: String) : String :=
  if string.isEmpty then 
    ""
  else
    let chars := string.toList
    let suffix_len := find_longest_palindromic_suffix string
    let prefix_len := chars.length - suffix_len
    let prefix := (chars.take prefix_len).reverse
    string ++ prefix.asString

-- LLM HELPER
lemma empty_is_palindrome : is_palindrome "" = true := by
  simp [is_palindrome]
  rfl

-- LLM HELPER  
lemma palindrome_reverse_eq (s: String) : is_palindrome s = true ↔ s = s.toList.reverse.asString := by
  simp [is_palindrome]

-- LLM HELPER
lemma string_prefix_of_itself (s: String) : s.isPrefixOf s = true := by
  simp [String.isPrefixOf]

-- LLM HELPER
lemma implementation_empty : implementation "" = "" := by
  simp [implementation]

-- LLM HELPER
lemma implementation_preserves_prefix (s: String) : s.isPrefixOf (implementation s) = true := by
  by_cases h : s.isEmpty
  · simp [implementation, h, String.isPrefixOf]
  · simp [implementation, h, String.isPrefixOf]
    have : s ++ (s.toList.take (s.length - find_longest_palindromic_suffix s)).reverse.asString = s ++ (s.toList.take (s.length - find_longest_palindromic_suffix s)).reverse.asString := rfl
    simp [String.isPrefixOf]
    exact String.isPrefixOf_append _ _

-- LLM HELPER
lemma implementation_is_palindrome (s: String) : is_palindrome (implementation s) = true := by
  by_cases h : s.isEmpty
  · simp [implementation, h]
    exact empty_is_palindrome
  · simp [implementation, h, is_palindrome]
    have : (s ++ (s.toList.take (s.length - find_longest_palindromic_suffix s)).reverse.asString).toList.reverse.asString = s ++ (s.toList.take (s.length - find_longest_palindromic_suffix s)).reverse.asString := by
      simp [List.reverse_append, List.reverse_reverse]
    exact this

-- LLM HELPER  
lemma implementation_length_ge (s: String) : s.length ≤ (implementation s).length := by
  by_cases h : s.isEmpty
  · simp [implementation, h]
    have : s.length = 0 := by simp [String.isEmpty_iff] at h; exact h
    simp [this]
  · simp [implementation, h]
    simp [String.length_append]
    exact Nat.le_add_right _ _

-- LLM HELPER
lemma implementation_is_shortest (s: String) (p: String) :
  s.isPrefixOf p = true → is_palindrome p = true → (implementation s).length ≤ p.length := by
  intro h_prefix h_palindrome
  by_cases h : s.isEmpty
  · simp [implementation, h]
    exact Nat.zero_le _
  · simp [implementation, h]
    have h_len : s.length ≤ p.length := by
      have := String.isPrefixOf_length h_prefix
      exact this
    simp [String.length_append]
    have : (s.toList.take (s.length - find_longest_palindromic_suffix s)).reverse.asString.length ≤ p.length - s.length := by
      have : find_longest_palindromic_suffix s ≤ s.length := by
        simp [find_longest_palindromic_suffix]
        apply List.foldl_le_of_le_init
        simp
      have : s.length - find_longest_palindromic_suffix s ≤ p.length - s.length := by
        omega
      simp [List.length_reverse, List.length_take]
      exact this
    omega

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
is_palindrome result = true ∧
result.length ≥ string.length ∧
string.isPrefixOf result = true ∧
-- comprehensive check that the result is the shortest palindrome
(∀ (possible_palindrome: String),
string.isPrefixOf possible_palindrome = true →
is_palindrome possible_palindrome = true →
result.length ≤ possible_palindrome.length);
-- program termination
∃ result, implementation string = result ∧
spec result

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · constructor
    · exact implementation_is_palindrome s
    · constructor
      · exact implementation_length_ge s
      · constructor
        · exact implementation_preserves_prefix s  
        · intros p h_prefix h_palindrome
          exact implementation_is_shortest s p h_prefix h_palindrome

-- #test implementation "" = ""
-- #test implementation "cat" = "catac"
-- #test implementation "cata" = "catac"