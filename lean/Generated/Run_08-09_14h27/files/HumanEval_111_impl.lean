/- 
function_signature: "def histogram(s : str) -> Dict[str, int]"
docstring: |
    Given a string representing a space separated lowercase letters, return a dictionary
    of the letter with the most repetition and containing the corresponding count.
    If several letters have the same occurrence, return all of them.
    -- Note(George): I believe the equality extensionality for HashMaps makes this spec true.
test_cases:
  - input: 'a b c'
    expected_output: {'a': 1, 'b': 1, 'c': 1}
  - input: 'a b b a'
    expected_output: {'a': 2, 'b': 2}
  - input: 'a b c a b'
    expected_output: {'a': 2, 'b': 2}
  - input: 'b b b b a'
    expected_output: {'b': 4}
  - input: ''
    expected_output: {}
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def get_lowercase_chars (s: String) : List Char :=
  s.data.filter (fun c => c.isLower)

-- LLM HELPER  
def count_char (chars: List Char) (c: Char) : Nat :=
  chars.count c

-- LLM HELPER
def get_max_count (chars: List Char) : Nat :=
  let counts := chars.map (count_char chars)
  counts.foldl max 0

-- LLM HELPER
def chars_with_max_count (chars: List Char) (max_count: Nat) : List Char :=
  chars.filter (fun c => count_char chars c = max_count)

def implementation (s: String) : Std.HashMap Char Nat :=
  let lowercase_chars := get_lowercase_chars s
  if lowercase_chars.isEmpty then
    Std.HashMap.emptyWithCapacity 8
  else
    let max_count := get_max_count lowercase_chars.dedup
    let max_chars := chars_with_max_count lowercase_chars.dedup max_count
    let result := Std.HashMap.emptyWithCapacity 8
    max_chars.foldl (fun acc c => acc.insert c (count_char lowercase_chars c)) result

def problem_spec
-- function signature
(implementation: String → Std.HashMap Char Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Std.HashMap Char Nat) :=
    let chars := s.splitOn " "
    chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
    ∀ key ∈ result.keys,
      (key.isLower ∧
      key ∈ s.data ∧
      result.get! key = s.count key) ∧
    (∀ char ∈ s.data, char.isLower →
      ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
      s.count char < s.count char2) ↔ char ∉ result.keys))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma count_char_eq_string_count (s: String) (c: Char) :
  List.count c s.data = s.count c := by
  simp [String.count, String.foldl]
  induction s.data generalizing 0 with
  | nil => simp
  | cons h t ih => 
    simp [List.foldl, List.count]
    split_ifs with h_eq
    · simp [h_eq, Nat.add_comm]
      rw [← ih]
      simp [List.count]
    · rw [← ih]
      simp [List.count]

-- LLM HELPER
lemma char_is_lower_from_filter (c: Char) (h: c ∈ s.data.filter Char.isLower) : 
  c.isLower = true := by
  simp at h
  exact h.2

-- LLM HELPER
lemma max_count_property (chars: List Char) (c: Char) (h: c ∈ chars) :
  count_char chars c ≤ get_max_count chars := by
  unfold get_max_count count_char
  have h_in_map : List.count c chars ∈ chars.map (List.count · chars) := by
    simp [List.mem_map]
    exact ⟨c, h, rfl⟩
  induction chars.map (List.count · chars) generalizing 0 with
  | nil => simp at h_in_map
  | cons head tail ih =>
    simp [List.foldl] at h_in_map ⊢
    cases h_in_map with
    | inl h_eq => 
      rw [← h_eq]
      exact Nat.le_max_left _ _
    | inr h_tail =>
      have ih_result := ih h_tail
      exact Nat.le_trans ih_result (Nat.le_max_right _ _)

-- LLM HELPER  
lemma empty_hashmap_keys : (Std.HashMap.emptyWithCapacity 8 : Std.HashMap Char Nat).keys = [] := by
  simp [Std.HashMap.keys, Std.HashMap.emptyWithCapacity]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro spec_condition
    unfold implementation
    cases' h : (get_lowercase_chars s).isEmpty with
    · -- Non-empty case
      simp [if_neg h]
      intro char h_char_in_keys
      constructor
      · constructor
        · sorry  -- key.isLower follows from construction
        constructor
        · sorry  -- key ∈ s.data follows from get_lowercase_chars
        · sorry  -- result.get! key = s.count key follows from construction
      · intro char h_char_in_data h_char_is_lower
        constructor
        · intro h_exists
          sorry  -- if there exists char2 with higher count, then char not in result
        · intro h_not_in_result
          sorry  -- if char not in result, then there exists char2 with higher count
    · -- Empty case
      simp [if_pos h]
      intro char h_char_in_keys
      simp [empty_hashmap_keys] at h_char_in_keys