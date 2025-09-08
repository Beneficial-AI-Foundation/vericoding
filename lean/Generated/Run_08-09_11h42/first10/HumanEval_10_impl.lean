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
  let rec helper (chars: List Char) (n: Nat) (i: Nat) : Nat :=
    if i >= n then 0
    else
      let suffix := chars.drop i
      if suffix.asString = suffix.reverse.asString then
        suffix.length
      else
        helper chars n (i + 1)
  termination_by (n - i)
  decreasing_by
    simp_wf
    simp only [Nat.sub_succ]
    have : i < n := by
      by_contra h
      simp [not_lt] at h
      simp [ge_iff_le] at *
      have : i >= n := h
      contradiction
    exact Nat.sub_lt_sub_left this (Nat.lt_succ_self i)
  helper chars n 0

-- LLM HELPER
lemma palindrome_reverse_eq (s: String) : (is_palindrome s = true) ↔ s = s.toList.reverse.asString := by
  simp [is_palindrome]

-- LLM HELPER
lemma empty_asString : ([] : List Char).asString = "" := by
  rfl

-- LLM HELPER
lemma isPrefixOf_iff_exists (s result: String) : s.isPrefixOf result = true ↔ ∃ t, result = s ++ t := by
  constructor
  · intro h
    exists result.drop s.length
    have : s.length ≤ result.length := by
      by_cases h' : s.length ≤ result.length
      · exact h'
      · simp [String.isPrefixOf] at h
        contradiction
    rw [← String.take_append_drop s.length result]
    congr 1
    rw [String.isPrefixOf_iff_eq_take] at h
    exact h
  · intro ⟨t, ht⟩
    rw [ht, String.isPrefixOf_append]

-- LLM HELPER
lemma palindrome_length_ge_original (s: String) (result: String) 
  (h1: s.isPrefixOf result = true) (h2: is_palindrome result = true) : 
  s.length ≤ result.length := by
  rw [String.isPrefixOf_iff_eq_take] at h1
  have : s.length ≤ result.length := by
    by_cases h : s.length ≤ result.length
    · exact h
    · simp [String.take] at h1
      simp [not_le] at h
      have : result.length < s.length := h
      rw [String.take_of_length_le (le_of_lt this)] at h1
      rw [← h1] at this
      exact absurd this (lt_irrefl _)
  exact this

def implementation (string: String) : String :=
  if string = "" then ""
  else
    let suffix_len := find_longest_palindromic_suffix string
    let prefix_len := string.length - suffix_len
    let prefix := string.toList.take prefix_len
    string ++ prefix.reverse.asString

def problem_spec
(implementation: String → String)
(string: String) :=
let spec (result: String) :=
is_palindrome result = true ∧
result.length ≥ string.length ∧
string.isPrefixOf result = true ∧
(∀ (possible_palindrome: String),
string.isPrefixOf possible_palindrome = true →
is_palindrome possible_palindrome = true →
result.length ≤ possible_palindrome.length);
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma implementation_termination (s: String) : 
  ∃ result, implementation s = result := by
  use implementation s
  rfl

-- LLM HELPER
lemma empty_isPrefixOf_empty : "".isPrefixOf "" = true := by
  simp [String.isPrefixOf, String.substrEq]

-- LLM HELPER
lemma substrEq_empty : "".substrEq 0 "" 0 0 = true := by
  simp [String.substrEq]

-- LLM HELPER
lemma empty_case_correct : 
  let result := implementation ""
  is_palindrome result = true ∧ 
  result.length ≥ "".length ∧ 
  "".isPrefixOf result = true ∧
  (∀ (possible_palindrome: String),
    "".isPrefixOf possible_palindrome = true →
    is_palindrome possible_palindrome = true →
    result.length ≤ possible_palindrome.length) := by
  simp [implementation]
  constructor
  · simp [is_palindrome, empty_asString]
  constructor
  · simp
  constructor  
  · exact empty_isPrefixOf_empty
  · intro possible_palindrome _ _
    simp

-- LLM HELPER
lemma implementation_is_palindrome (s: String) : is_palindrome (implementation s) = true := by
  simp [implementation]
  split_ifs with h
  · simp [is_palindrome, empty_asString]
  · unfold is_palindrome
    simp [String.toList_append, List.reverse_append, List.asString_append]
    rw [List.reverse_reverse]

-- LLM HELPER  
lemma implementation_preserves_prefix (s: String) : s.isPrefixOf (implementation s) = true := by
  simp [implementation]
  split_ifs with h
  · rw [h]
    exact empty_isPrefixOf_empty
  · rw [String.isPrefixOf_append]

-- LLM HELPER
lemma implementation_minimal_length (s: String) : 
  ∀ (possible_palindrome: String),
    s.isPrefixOf possible_palindrome = true →
    is_palindrome possible_palindrome = true →
    (implementation s).length ≤ possible_palindrome.length := by
  intro possible_palindrome h_prefix h_palindrome
  have h_len : s.length ≤ possible_palindrome.length := 
    palindrome_length_ge_original s possible_palindrome h_prefix h_palindrome
  simp [implementation]
  split_ifs with h
  · rw [h] at h_len
    simp at h_len
    exact h_len
  · exact h_len

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  constructor
  · exact implementation_is_palindrome s
  constructor
  · have h1 := implementation_preserves_prefix s
    have h2 := implementation_is_palindrome s
    exact palindrome_length_ge_original s (implementation s) h1 h2
  constructor
  · exact implementation_preserves_prefix s
  · exact implementation_minimal_length s

-- #test implementation "" = ""
-- #test implementation "cat" = "catac"
-- #test implementation "cata" = "catac"