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
  rfl

-- LLM HELPER
lemma char_is_lower_from_filter (c: Char) (h: c ∈ s.data.filter Char.isLower) : 
  c.isLower = true := by
  simp [List.mem_filter] at h
  exact h.2

-- LLM HELPER
lemma max_count_property (chars: List Char) (c: Char) (h: c ∈ chars) :
  count_char chars c ≤ get_max_count chars := by
  unfold get_max_count
  simp [List.le_foldl_max]
  exact ⟨c, h, rfl⟩

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
      intro char h_char_in_keys
      simp [if_neg h] at h_char_in_keys
      constructor
      · constructor
        · constructor
          · -- char.isLower = true
            have : char ∈ chars_with_max_count (get_lowercase_chars s).dedup (get_max_count (get_lowercase_chars s).dedup) := by
              simp [Std.HashMap.mem_keys] at h_char_in_keys
              exact h_char_in_keys
            unfold chars_with_max_count at this
            simp [List.mem_filter] at this
            have : char ∈ (get_lowercase_chars s).dedup := this.1
            have : char ∈ get_lowercase_chars s := List.mem_of_mem_dedup this
            exact char_is_lower_from_filter char this
          · -- char ∈ s.data
            have : char ∈ chars_with_max_count (get_lowercase_chars s).dedup (get_max_count (get_lowercase_chars s).dedup) := by
              simp [Std.HashMap.mem_keys] at h_char_in_keys
              exact h_char_in_keys
            unfold chars_with_max_count at this
            simp [List.mem_filter] at this
            have : char ∈ (get_lowercase_chars s).dedup := this.1
            have : char ∈ get_lowercase_chars s := List.mem_of_mem_dedup this
            unfold get_lowercase_chars at this
            simp [List.mem_filter] at this
            exact this.1
        · -- result.get! key = s.count key
          simp [Std.HashMap.get!]
          rw [← count_char_eq_string_count]
          simp
      · intro char h_char_in_data h_char_lower
        constructor
        · intro h_exists_greater
          -- If there exists a char with greater count, then char is not in result
          simp [Std.HashMap.mem_keys]
          intro h_in_max_chars
          have : count_char (get_lowercase_chars s) char = get_max_count (get_lowercase_chars s).dedup := by
            unfold chars_with_max_count at h_in_max_chars
            simp [List.mem_filter] at h_in_max_chars
            exact h_in_max_chars.2
          obtain ⟨char2, h_char2_in_data, h_char2_lower, h_char2_neq, h_count_lt⟩ := h_exists_greater
          have : count_char (get_lowercase_chars s) char2 > count_char (get_lowercase_chars s) char := by
            rw [count_char_eq_string_count, count_char_eq_string_count]
            exact h_count_lt
          have : count_char (get_lowercase_chars s) char2 ≤ get_max_count (get_lowercase_chars s).dedup := by
            apply max_count_property
            simp [List.mem_dedup]
            unfold get_lowercase_chars
            simp [List.mem_filter]
            constructor
            · exact h_char2_in_data
            · exact h_char2_lower
          linarith
        · intro h_not_in_keys
          -- If char is not in result, then there exists a char with greater count
          simp [Std.HashMap.mem_keys] at h_not_in_keys
          unfold chars_with_max_count at h_not_in_keys
          simp [List.mem_filter] at h_not_in_keys
          push_neg at h_not_in_keys
          have char_in_dedup : char ∈ (get_lowercase_chars s).dedup := by
            simp [List.mem_dedup]
            unfold get_lowercase_chars
            simp [List.mem_filter]
            exact ⟨h_char_in_data, h_char_lower⟩
          have : count_char (get_lowercase_chars s) char ≠ get_max_count (get_lowercase_chars s).dedup :=
            h_not_in_keys char_in_dedup
          have : count_char (get_lowercase_chars s) char < get_max_count (get_lowercase_chars s).dedup := by
            have le := max_count_property (get_lowercase_chars s).dedup char char_in_dedup
            unfold count_char at le this
            simp [List.count_dedup] at le
            exact Nat.lt_of_le_of_ne le this
          -- Now find a character that achieves the maximum
          have max_exists : ∃ c ∈ (get_lowercase_chars s).dedup, count_char (get_lowercase_chars s).dedup c = get_max_count (get_lowercase_chars s).dedup := by
            simp [get_max_count]
            have : ((get_lowercase_chars s).dedup.map (count_char (get_lowercase_chars s).dedup)).length > 0 := by
              simp [List.length_pos_iff_exists_mem, List.mem_map]
              use char
              exact char_in_dedup
            exact List.exists_mem_eq_foldl_max _ this
          obtain ⟨c, hc_mem, hc_max⟩ := max_exists
          use c
          constructor
          · have : c ∈ get_lowercase_chars s := List.mem_of_mem_dedup hc_mem
            unfold get_lowercase_chars at this
            simp [List.mem_filter] at this
            exact this.1
          constructor
          · have : c ∈ get_lowercase_chars s := List.mem_of_mem_dedup hc_mem
            exact char_is_lower_from_filter c this
          constructor
          · have : c ∈ get_lowercase_chars s := List.mem_of_mem_dedup hc_mem
            unfold get_lowercase_chars at this
            simp [List.mem_filter] at this
            have : c ≠ char := by
              intro heq
              subst heq
              rw [hc_max] at this
              unfold count_char at this
              simp [List.count_dedup] at this
              exact Nat.lt_irrefl _ this
            exact this
          · rw [count_char_eq_string_count, count_char_eq_string_count]
            have : count_char (get_lowercase_chars s) c = count_char (get_lowercase_chars s).dedup c := by
              unfold count_char
              rw [List.count_dedup]
            rw [this, hc_max]
            have : count_char (get_lowercase_chars s) char = count_char (get_lowercase_chars s).dedup char := by
              unfold count_char
              rw [List.count_dedup]
            rw [this]
            exact this
    · -- Empty case
      rw [if_pos h]
      intro char h_char_in_keys
      simp [Std.HashMap.keys_emptyWithCapacity] at h_char_in_keys