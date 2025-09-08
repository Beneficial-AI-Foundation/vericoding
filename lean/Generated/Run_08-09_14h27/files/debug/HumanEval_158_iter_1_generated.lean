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
  let characters := string_idx.image (fun i => string.toList[i]!);
  characters.card;
-- spec
let spec (result: String) :=
(result = "" ↔ words.length = 0) ∧
(words.length != 0 → result ∈ words ∧
let unique_chars_list := words.map unique_chars;
let max_unique_chars := unique_chars_list.max?.get!;
unique_chars result = max_unique_chars ∧
∀ i : Nat, i < words.length →
  unique_chars_list[i]! = max_unique_chars →
  result ≤ words[i]!);
-- program terminates
∃ result, impl words = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma unique_chars_eq_unique_chars_count (s: String) :
  let unique_chars := fun (string: String) =>
    let string_idx := {i: Nat | i < string.length}.toFinset;
    let characters := string_idx.image (fun i => string.toList[i]!);
    characters.card;
  unique_chars s = unique_chars_count s := by
  simp [unique_chars_count]
  congr 1
  ext c
  simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq, List.get!_eq_get?]
  constructor
  · intro ⟨i, hi, h⟩
    rw [← h]
    simp [String.toList]
    use i
    simp [hi]
    have : i < s.toList.length := by simp [String.toList]; exact hi
    rw [List.get?_eq_get this]
    simp [String.toList]
  · intro h
    simp [List.mem_toList] at h
    obtain ⟨i, hi, h_eq⟩ := h
    use i
    constructor
    · simp [String.toList] at hi; exact hi
    · simp [String.toList] at h_eq; exact h_eq.symm

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
    · simp [List.foldl]
      by_cases h1 : unique_chars_count t > unique_chars_count head
      · simp [h1]
        right
        exact ih
      · simp [h1]
        by_cases h2 : unique_chars_count t = unique_chars_count head ∧ t < head
        · simp [h2]
          right  
          exact ih
        · simp [h2]
          cases ih
          · left; assumption
          · right; assumption

theorem correctness
(words: List String)
: problem_spec implementation words := by
  simp [problem_spec, implementation]
  use find_best_word words
  constructor
  · rfl
  · simp only [find_best_word_empty]
    constructor
    · rfl
    · intro h
      constructor
      · exact find_best_word_mem words h
      · constructor
        · simp [unique_chars_eq_unique_chars_count]
          sorry
        · intro i hi h_max
          simp [unique_chars_eq_unique_chars_count] at h_max ⊢
          sorry

-- #test implementation ["name", "of", "string"]= "string"
-- #test implementation ["name", "enam", "game"] = "enam"  
-- #test implementation ["aaaaaaa", "bb" ,"cc"] = "aaaaaaa"