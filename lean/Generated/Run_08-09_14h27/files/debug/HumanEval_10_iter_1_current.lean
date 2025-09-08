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

-- LLM HELPER
def make_palindrome_aux (s: String) : String :=
  if s.isEmpty then ""
  else
    let chars := s.toList
    let suffix_len := find_longest_palindromic_suffix s
    let prefix_len := chars.length - suffix_len
    let prefix := (chars.take prefix_len).reverse
    s ++ prefix.asString

def implementation (string: String) : String :=
  make_palindrome_aux string

-- LLM HELPER
lemma empty_is_palindrome : is_palindrome "" = true := by
  simp [is_palindrome]

-- LLM HELPER  
lemma palindrome_reverse_eq (s: String) : is_palindrome s = true ↔ s = s.toList.reverse.asString := by
  simp [is_palindrome]

-- LLM HELPER
lemma string_prefix_of_itself (s: String) : s.isPrefixOf s := by
  simp [String.isPrefixOf]

-- LLM HELPER
lemma implementation_empty : implementation "" = "" := by
  simp [implementation, make_palindrome_aux]

-- LLM HELPER
lemma find_longest_palindromic_suffix_le (s: String) : 
  find_longest_palindromic_suffix s ≤ s.length := by
  sorry

-- LLM HELPER
lemma implementation_preserves_prefix (s: String) : s.isPrefixOf (implementation s) := by
  cases' s.isEmpty with h
  · simp [implementation, make_palindrome_aux]
    exact string_prefix_of_itself s
  · simp [implementation, make_palindrome_aux, h]
    simp [String.isPrefixOf]
    sorry

-- LLM HELPER
lemma implementation_is_palindrome (s: String) : is_palindrome (implementation s) = true := by
  sorry

-- LLM HELPER  
lemma implementation_length_ge (s: String) : s.length ≤ (implementation s).length := by
  sorry

-- LLM HELPER
lemma implementation_is_shortest (s: String) (p: String) :
  s.isPrefixOf p → is_palindrome p = true → (implementation s).length ≤ p.length := by
  sorry

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
      · exact Nat.le_of_lt_succ (Nat.lt_succ_of_le (implementation_length_ge s))
      · constructor
        · exact implementation_preserves_prefix s  
        · intros p h_prefix h_palindrome
          have h_pal : is_palindrome p = true := h_palindrome
          exact implementation_is_shortest s p h_prefix h_pal

-- #test implementation "" = ""
-- #test implementation "cat" = "catac"
-- #test implementation "cata" = "catac"