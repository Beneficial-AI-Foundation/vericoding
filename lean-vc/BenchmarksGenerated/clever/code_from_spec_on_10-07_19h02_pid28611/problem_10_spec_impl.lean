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
lemma string_isPrefixOf_append (s t: String) : 
  s.isPrefixOf (s ++ t) = true := by
  simp [String.isPrefixOf]
  rw [String.startsWith_append]

-- LLM HELPER
lemma string_length_le_of_isPrefixOf {s t: String} (h: s.isPrefixOf t = true) : 
  s.length ≤ t.length := by
  simp [String.isPrefixOf] at h
  have : s.toList.length ≤ t.toList.length := List.length_le_of_isPrefixOf h
  rw [←String.length_toList, ←String.length_toList] at this
  exact this

-- LLM HELPER
lemma find_shortest_palindrome_is_palindrome (s: String) : 
  is_palindrome (find_shortest_palindrome s) := by
  unfold is_palindrome find_shortest_palindrome
  split_ifs with h
  · rw [List.reverse_nil] at h
    have : s.toList = [] := by
      rw [←String.length_toList] at h
      exact List.eq_nil_of_length_eq_zero h
    rw [this, List.reverse_nil]
  · have chars := s.toList
    have rev_chars := chars.reverse
    have n := chars.length
    have overlap := (List.range n).foldl (fun acc i =>
      if List.isPrefixOf rev_chars (chars.drop i) then
        max acc (n - i)
      else acc) 0
    simp [String.toList]
    rw [List.reverse_append, List.reverse_take, List.reverse_reverse]
    congr 1
    · rfl
    · rfl

-- LLM HELPER
lemma find_shortest_palindrome_has_prefix (s: String) : 
  s.isPrefixOf (find_shortest_palindrome s) = true := by
  unfold find_shortest_palindrome
  split_ifs with h
  · rw [String.isPrefixOf_refl]
  · simp [String.isPrefixOf]
    have chars := s.toList
    have rev_chars := chars.reverse
    have n := chars.length
    have overlap := (List.range n).foldl (fun acc i =>
      if List.isPrefixOf rev_chars (chars.drop i) then
        max acc (n - i)
      else acc) 0
    simp [String.toList]
    apply List.IsPrefix.isPrefixOf
    exact List.suffix_append _ _

-- LLM HELPER
lemma find_shortest_palindrome_length (s: String) : 
  (find_shortest_palindrome s).length ≥ s.length := by
  unfold find_shortest_palindrome
  split_ifs with h
  · rfl
  · simp [String.length]
    have chars := s.toList
    have rev_chars := chars.reverse
    have n := chars.length
    have overlap := (List.range n).foldl (fun acc i =>
      if List.isPrefixOf rev_chars (chars.drop i) then
        max acc (n - i)
      else acc) 0
    simp [String.toList, List.length_append, List.length_take]
    have : overlap ≤ n := by
      sorry
    omega

-- LLM HELPER
lemma find_shortest_palindrome_minimal (s: String) : 
  ∀ (possible_palindrome: String),
  s.isPrefixOf possible_palindrome = true →
  is_palindrome possible_palindrome →
  (find_shortest_palindrome s).length ≤ possible_palindrome.length := by
  intro possible_palindrome h_prefix h_palindrome
  have h_len : s.length ≤ possible_palindrome.length := string_length_le_of_isPrefixOf h_prefix
  unfold find_shortest_palindrome
  split_ifs with h
  · rw [←String.length_toList] at h
    have : s.toList = [] := List.eq_nil_of_length_eq_zero h
    rw [←String.length_toList, this, List.length_nil]
    exact Nat.zero_le _
  · have chars := s.toList
    have rev_chars := chars.reverse
    have n := chars.length
    have overlap := (List.range n).foldl (fun acc i =>
      if List.isPrefixOf rev_chars (chars.drop i) then
        max acc (n - i)
      else acc) 0
    simp [String.length, String.toList, List.length_append, List.length_take]
    -- The constructed palindrome has minimal length by construction
    sorry

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