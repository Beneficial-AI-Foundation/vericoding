import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def is_palindrome (s: String) : Prop :=
  s.toList = s.toList.reverse

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
def reverse_string (s: String) : String :=
  String.mk (s.toList.reverse)

-- LLM HELPER
def find_shortest_palindrome (s: String) : String :=
  s ++ reverse_string s

def implementation (string: String) : String := 
  find_shortest_palindrome string

-- LLM HELPER
lemma reverse_string_correct (s: String) : 
  (reverse_string s).toList = s.toList.reverse := by
  unfold reverse_string
  simp

-- LLM HELPER
lemma is_palindrome_iff (s: String) : 
  is_palindrome s ↔ s.toList = s.toList.reverse := by
  rfl

-- LLM HELPER
lemma string_append_toList (s t: String) : 
  (s ++ t).toList = s.toList ++ t.toList := by
  exact String.toList_append s t

-- LLM HELPER
lemma string_isPrefixOf_append (s t: String) : 
  s.isPrefixOf (s ++ t) = true := by
  unfold String.isPrefixOf
  rw [string_append_toList]
  exact List.isPrefixOf_append _ _

-- LLM HELPER
lemma string_length_append (s t: String) : 
  (s ++ t).length = s.length + t.length := by
  exact String.length_append s t

-- LLM HELPER
lemma string_length_le_of_isPrefixOf {s t: String} (h: s.isPrefixOf t = true) : 
  s.length ≤ t.length := by
  unfold String.isPrefixOf at h
  simp at h
  have : s.toList.length ≤ t.toList.length := List.length_le_of_isPrefixOf h
  rw [String.length_toList] at this
  exact this

-- LLM HELPER
lemma find_shortest_palindrome_is_palindrome (s: String) : 
  is_palindrome (find_shortest_palindrome s) := by
  unfold is_palindrome find_shortest_palindrome
  rw [string_append_toList, reverse_string_correct]
  rw [List.reverse_append, List.reverse_reverse]

-- LLM HELPER
lemma find_shortest_palindrome_has_prefix (s: String) : 
  s.isPrefixOf (find_shortest_palindrome s) = true := by
  unfold find_shortest_palindrome
  exact string_isPrefixOf_append s (reverse_string s)

-- LLM HELPER
lemma find_shortest_palindrome_length (s: String) : 
  (find_shortest_palindrome s).length ≥ s.length := by
  unfold find_shortest_palindrome
  rw [string_length_append]
  exact Nat.le_add_right s.length (reverse_string s).length

-- LLM HELPER
lemma reverse_string_length (s: String) : 
  (reverse_string s).length = s.length := by
  unfold reverse_string
  simp

-- LLM HELPER
lemma find_shortest_palindrome_minimal (s: String) : 
  ∀ (possible_palindrome: String),
  s.isPrefixOf possible_palindrome = true →
  is_palindrome possible_palindrome →
  (find_shortest_palindrome s).length ≤ possible_palindrome.length := by
  intro possible_palindrome h_prefix h_palindrome
  unfold find_shortest_palindrome
  rw [string_length_append, reverse_string_length]
  have h_len : s.length ≤ possible_palindrome.length := by
    exact string_length_le_of_isPrefixOf h_prefix
  have h_double : s.length + s.length ≤ possible_palindrome.length + possible_palindrome.length := by
    linarith
  have h_not_less : ¬(s.length + s.length > possible_palindrome.length) := by
    linarith [h_len]
  linarith [h_len]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  use find_shortest_palindrome s
  constructor
  · rfl
  · constructor
    · exact find_shortest_palindrome_is_palindrome s
    · constructor
      · exact find_shortest_palindrome_length s
      · constructor
        · exact find_shortest_palindrome_has_prefix s
        · exact find_shortest_palindrome_minimal s