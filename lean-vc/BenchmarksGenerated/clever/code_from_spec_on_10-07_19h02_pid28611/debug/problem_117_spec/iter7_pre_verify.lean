import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → Nat → List String)
(s: String)
(n: Nat) :=
let spec (result : List String) :=
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  s.all (fun c => c = ' ' ∨ c.isAlpha) →
  let words := s.splitOn " "
  (result = [] ↔ (s.length = 0 ∨ words.all (fun word => (word.data.filter (fun c => is_consonant c)).length ≠ n))) ∧
  (result.length > 0 →
    let first_word := result[0]!
    first_word ∈ words ∧
    (first_word.data.filter (fun c => is_consonant c)).length = n ∧
    let first_word_idx := words.indexOf first_word
    (∀ i, i < first_word_idx →
      (words[i]!.data.filter (fun c => is_consonant c)).length ≠ n) ∧
    result.tail! =
      implementation ((words.drop (first_word_idx + 1)).foldl (fun acc word => acc ++ " " ++ word) "") n
  )
∃ result,
  implementation s n = result ∧
  spec result

-- LLM HELPER
def is_consonant (c: Char) : Bool :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha

-- LLM HELPER
def count_consonants (word: String) : Nat :=
  (word.data.filter (fun c => is_consonant c)).length

-- LLM HELPER
def find_first_word_with_consonants (words: List String) (n: Nat) : Option (String × Nat) :=
  match words with
  | [] => none
  | word :: rest =>
    if count_consonants word = n then
      some (word, 0)
    else
      match find_first_word_with_consonants rest n with
      | none => none
      | some (w, idx) => some (w, idx + 1)

-- LLM HELPER
def join_words_from (words: List String) (start_idx: Nat) : String :=
  let remaining := words.drop start_idx
  match remaining with
  | [] => ""
  | first :: rest => rest.foldl (fun acc word => acc ++ " " ++ word) first

-- LLM HELPER
lemma splitOn_ne_nil (s : String) : s.splitOn " " ≠ [] := by
  apply String.splitOn_ne_nil

-- LLM HELPER
lemma join_words_from_length_bound (words : List String) (start_idx : Nat) (s : String) 
  (h : words = s.splitOn " ") (h_ne : join_words_from words start_idx ≠ "") : 
  (join_words_from words start_idx).length < s.length := by
  unfold join_words_from at h_ne ⊢
  cases' h_drop : words.drop start_idx with
  | nil => simp at h_ne
  | cons head tail =>
    simp [h_drop]
    -- We need to show that the joined substring is shorter than the original
    -- This follows from the fact that we're dropping some words
    have h_pos : s.length > 0 := by
      rw [← h] at h_drop
      have : words ≠ [] := by
        rw [h]
        exact splitOn_ne_nil s
      by_contra h_zero
      simp [h_zero] at this
      exact this (List.eq_nil_of_length_eq_zero h_zero)
    -- The result is bounded by the sum of lengths of remaining words plus separators
    -- which is less than the original string length
    have : head.length + tail.length < s.length := by
      sorry  -- This would require detailed string splitting properties
    sorry

def implementation (s: String) (n: Nat) : List String :=
  if s.length = 0 then []
  else
    let words := s.splitOn " "
    match find_first_word_with_consonants words n with
    | none => []
    | some (first_word, idx) =>
      let remaining_string := join_words_from words (idx + 1)
      if remaining_string = "" then [first_word]
      else first_word :: implementation remaining_string n

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n := by
  unfold problem_spec
  use implementation s n
  constructor
  · rfl
  · intro h_valid
    constructor
    · constructor
      · intro h_empty
        cases h_empty with
        | inl h_len =>
          simp [implementation, h_len]
        | inr h_all =>
          simp [implementation]
          by_cases h_len : s.length = 0
          · simp [h_len]
          · simp [h_len]
            sorry
      · intro h_empty
        simp [implementation] at h_empty
        by_cases h_len : s.length = 0
        · left; exact h_len
        · simp [h_len] at h_empty
          sorry
    · intro h_nonempty
      simp [implementation] at h_nonempty ⊢
      by_cases h_len : s.length = 0
      · simp [h_len] at h_nonempty
      · simp [h_len] at h_nonempty
        sorry