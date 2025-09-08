/- 
function_signature: "def find_max(words: List String) -> String"
docstring: |
    Write a function that accepts a list of strings.
    The list contains different words. Return the word with maximum number
    of unique characters. If multiple strings have maximum number of unique
    characters, return the one which comes first in lexicographical order.
test_cases:
  - input: ["name", "of", "string"]
    expected_output: "string"
  - input: ["name", "enam", "game"]
    expected_output: "enam"
  - input: ["aaaaaaa", "bb", "cc"]
    expected_output: "aaaaaaa"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def unique_chars_count (s: String) : Nat :=
  s.toList.toFinset.card

-- LLM HELPER
def find_best_word (words: List String) : String :=
  match words with
  | [] => ""
  | head :: tail =>
    tail.foldl (fun acc word =>
      let acc_count := unique_chars_count acc
      let word_count := unique_chars_count word
      if word_count > acc_count then word
      else if word_count = acc_count ∧ word < acc then word
      else acc
    ) head

def implementation (words: List String) : String :=
  find_best_word words

def problem_spec
-- function signature
(impl: List String → String)
-- inputs
(words: List String) :=
let unique_chars (string: String) :=
  let string_idx := {i: Nat | i < string.length}.toFinset;
  let characters := string_idx.image (fun i => string.data[i]?.getD 'A');
  characters.card;
-- spec
let spec (result: String) :=
(result = "" ↔ words = []) ∧
(words ≠ [] → result ∈ words ∧
let unique_chars_list := words.map unique_chars;
let max_unique_chars := unique_chars_list.max?.get!;
unique_chars result = max_unique_chars ∧
∀ i : Nat, i < words.length →
  unique_chars_list[i]?.getD 0 = max_unique_chars →
  result.data ≤ (words[i]?.getD "").data);
-- program terminates
∃ result, impl words = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma unique_chars_eq_unique_chars_count (s: String) :
  let unique_chars := fun (string: String) =>
    let string_idx := {i: Nat | i < string.length}.toFinset;
    let characters := string_idx.image (fun i => string.data[i]?.getD 'A');
    characters.card;
  unique_chars s = unique_chars_count s := by
  simp only [unique_chars_count]
  congr 1
  ext c
  constructor
  · intro h
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq] at h
    obtain ⟨i, hi, h_eq⟩ := h
    rw [← h_eq]
    simp only [List.mem_toFinset]
    rw [List.mem_iff_get]
    use i
    rw [List.get?_eq_get]
    · rw [h_eq]
      rfl
    · exact hi
  · intro h
    simp only [List.mem_toFinset] at h
    rw [List.mem_iff_get] at h
    obtain ⟨i, h_eq⟩ := h
    simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq]
    use i
    constructor
    · simp only [String.length]
      rw [← List.get?_eq_some_iff]
      exact List.get?_eq_get.symm ▸ ⟨h_eq⟩
    · simp only [String.data] at h_eq ⊢
      rw [List.get?_eq_get]
      · exact h_eq
      · simp only [String.length]
        rw [← List.get?_eq_some_iff]
        exact List.get?_eq_get.symm ▸ ⟨h_eq⟩

-- LLM HELPER
lemma find_best_word_empty : find_best_word [] = "" := by
  simp [find_best_word]

-- LLM HELPER  
lemma find_best_word_mem (words: List String) (h: words ≠ []) :
  find_best_word words ∈ words := by
  cases' words with head tail
  · contradiction
  · simp [find_best_word]
    induction' tail with t ts ih generalizing head
    · simp
    · simp only [List.foldl, List.mem_cons]
      by_cases h1 : unique_chars_count t > unique_chars_count head
      · simp [h1]
        right
        have h_nonempty : t :: ts ≠ [] := by simp
        have ih_applied := ih (if unique_chars_count head < unique_chars_count t then t else head) h_nonempty
        simp [h1] at ih_applied
        exact ih_applied
      · simp [h1]
        by_cases h2 : unique_chars_count t = unique_chars_count head ∧ t < head
        · simp [h2]
          right  
          have h_nonempty : t :: ts ≠ [] := by simp
          have ih_applied := ih (if unique_chars_count head < unique_chars_count t then t 
                                 else if unique_chars_count t = unique_chars_count head ∧ t < head then t 
                                 else head) h_nonempty
          simp [h1, h2] at ih_applied
          exact ih_applied
        · simp [h2]
          have h_nonempty : head :: ts ≠ [] := by simp
          have ih_applied := ih (if unique_chars_count head < unique_chars_count t then t 
                                 else if unique_chars_count t = unique_chars_count head ∧ t < head then t 
                                 else head) h_nonempty
          simp [h1, h2] at ih_applied
          cases ih_applied with
          | inl h_left => left; exact h_left
          | inr h_right => right; right; exact h_right

theorem correctness
(words: List String)
: problem_spec implementation words := by
  simp [problem_spec, implementation]
  use find_best_word words
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        rw [h, find_best_word_empty]
      · intro h
        cases' words with head tail
        · contradiction
        · simp [find_best_word_empty]
    · intro h
      constructor
      · exact find_best_word_mem words h
      · constructor
        · simp [unique_chars_eq_unique_chars_count]
          sorry
        · intro i h_len h_max
          simp [unique_chars_eq_unique_chars_count] at h_max ⊢
          sorry