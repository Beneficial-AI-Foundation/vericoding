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
def overlap_suffix (s: String) : Nat :=
  let chars := s.toList
  let n := chars.length
  (List.range n).foldl (fun acc i =>
    if List.isPrefixOf chars.reverse (chars.drop i) then
      max acc (n - i)
    else acc) 0

-- LLM HELPER
def find_shortest_palindrome (s: String) : String :=
  if s.length = 0 then s
  else
    let chars := s.toList
    let rev_chars := chars.reverse
    let n := chars.length
    let overlap := (List.range n).foldl (fun acc i =>
      if List.isPrefixOf rev_chars (chars.drop i) then
        max acc (n - i)
      else acc) 0
    String.mk (rev_chars.take (n - overlap) ++ chars)

def implementation (string: String) : String := 
  find_shortest_palindrome string

-- LLM HELPER
lemma string_append_toList (s t: String) : 
  (s ++ t).toList = s.toList ++ t.toList := by
  cases s with
  | mk s_data =>
    cases t with
    | mk t_data =>
      simp [String.append, String.toList]

-- LLM HELPER
lemma string_isPrefixOf_append (s t: String) : 
  s.isPrefixOf (s ++ t) = true := by
  simp [String.isPrefixOf]
  exact String.startsWith_append s t

-- LLM HELPER
lemma string_length_le_of_isPrefixOf {s t: String} (h: s.isPrefixOf t = true) : 
  s.length ≤ t.length := by
  have : s.toList.isPrefixOf t.toList := by
    simp [String.isPrefixOf] at h
    exact h
  have : s.toList.length ≤ t.toList.length := List.length_le_of_isPrefixOf this
  simp [String.length] at this
  exact this

-- LLM HELPER
lemma find_shortest_palindrome_is_palindrome (s: String) : 
  is_palindrome (find_shortest_palindrome s) := by
  unfold is_palindrome find_shortest_palindrome
  split_ifs with h
  · simp [h]
  · simp [String.toList]
    have chars := s.toList
    have rev_chars := chars.reverse
    have n := chars.length
    have overlap := (List.range n).foldl (fun acc i =>
      if List.isPrefixOf rev_chars (chars.drop i) then
        max acc (n - i)
      else acc) 0
    simp [List.reverse_append, List.reverse_take, List.reverse_reverse]
    sorry

-- LLM HELPER
lemma find_shortest_palindrome_has_prefix (s: String) : 
  s.isPrefixOf (find_shortest_palindrome s) = true := by
  unfold find_shortest_palindrome
  split_ifs with h
  · simp [h]
  · simp [String.isPrefixOf]
    sorry

-- LLM HELPER
lemma find_shortest_palindrome_length (s: String) : 
  (find_shortest_palindrome s).length ≥ s.length := by
  unfold find_shortest_palindrome
  split_ifs with h
  · simp [h]
  · simp [String.length]
    sorry

-- LLM HELPER
lemma find_shortest_palindrome_minimal (s: String) : 
  ∀ (possible_palindrome: String),
  s.isPrefixOf possible_palindrome = true →
  is_palindrome possible_palindrome →
  (find_shortest_palindrome s).length ≤ possible_palindrome.length := by
  intro possible_palindrome h_prefix h_palindrome
  have h_len : s.length ≤ possible_palindrome.length := by
    exact string_length_le_of_isPrefixOf h_prefix
  unfold find_shortest_palindrome
  split_ifs with h
  · simp [h] at h_len
    exact h_len
  · sorry

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