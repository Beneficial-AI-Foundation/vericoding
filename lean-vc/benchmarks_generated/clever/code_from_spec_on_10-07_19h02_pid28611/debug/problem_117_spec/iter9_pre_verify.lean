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
lemma string_splitOn_empty_iff (s : String) : s.splitOn " " = [] ↔ s = "" := by
  constructor
  · intro h
    by_contra h_ne
    have : s.length > 0 := by
      rw [← String.length_pos_iff_ne_empty]
      exact h_ne
    have : s.splitOn " " ≠ [] := by
      rw [← List.length_pos_iff_ne_nil]
      have : s.splitOn " " = s.split (· = ' ') := rfl
      sorry
    contradiction
  · intro h
    rw [h]
    simp [String.splitOn]

-- LLM HELPER
lemma join_words_from_length_lt (words : List String) (idx : Nat) (s : String) :
  words = s.splitOn " " → s.length > 0 → join_words_from words (idx + 1) ≠ "" →
  (join_words_from words (idx + 1)).length < s.length := by
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
termination_by s.length
decreasing_by
  · simp_wf
    apply join_words_from_length_lt
    · rfl
    · simp only [ite_neg, not_false_eq_true]
      assumption
    · assumption

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
          unfold implementation
          simp [h_len]
        | inr h_all =>
          unfold implementation
          by_cases h_len : s.length = 0
          · simp [h_len]
          · simp [h_len]
            sorry
      · intro h_empty
        unfold implementation at h_empty
        by_cases h_len : s.length = 0
        · constructor
          exact h_len
        · simp [h_len] at h_empty
          apply Or.inr
          sorry
    · intro h_nonempty
      unfold implementation at h_nonempty ⊢
      by_cases h_len : s.length = 0
      · simp [h_len] at h_nonempty
      · simp [h_len] at h_nonempty
        sorry