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
lemma join_words_from_length_bound (words: List String) (start_idx: Nat) :
  join_words_from words (start_idx + 1) = "" ∨ 
  (join_words_from words (start_idx + 1)).length < (words.foldl (fun acc word => acc ++ " " ++ word) "").length := by
  unfold join_words_from
  simp
  by_cases h : words.drop (start_idx + 1) = []
  · simp [h]
  · right
    have : start_idx + 1 > 0 := by simp
    have : words.drop (start_idx + 1) ≠ [] := h
    have : words.drop (start_idx + 1) ⊆ words := List.drop_subset _ _
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
  simp_wf
  unfold join_words_from
  simp
  have h_drop : words.drop (idx + 1) ≠ [] ∨ words.drop (idx + 1) = [] := by tauto
  cases h_drop with
  | inl h_ne =>
    have : (words.drop (idx + 1)).length < words.length := by
      apply List.length_drop_lt_length_of_ne_nil
      · exact h_ne
      · rw [List.splitOn_ne_nil]
        simp
        exact h✝
    sorry
  | inr h_eq =>
    simp [h_eq]

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
            by_cases h_find : find_first_word_with_consonants (s.splitOn " ") n = none
            · simp [h_find]
            · simp [h_find]
              obtain ⟨word, idx⟩ := h_find
              exfalso
              have h_mem : word ∈ s.splitOn " " := by
                sorry
              have h_count : count_consonants word = n := by
                sorry
              have h_all_spec : (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length ≠ n := by
                apply h_all
                exact h_mem
              rw [← count_consonants_eq] at h_all_spec
              exact h_all_spec h_count
      · intro h_empty
        simp [implementation] at h_empty
        by_cases h_len : s.length = 0
        · left; exact h_len
        · simp [h_len] at h_empty
          by_cases h_find : find_first_word_with_consonants (s.splitOn " ") n = none
          · simp [h_find] at h_empty
          · simp [h_find] at h_empty
            obtain ⟨word, idx⟩ := h_find
            simp at h_empty
            by_cases h_remaining : join_words_from (s.splitOn " ") (idx + 1) = ""
            · simp [h_remaining] at h_empty
            · simp [h_remaining] at h_empty
    · intro h_nonempty
      simp [implementation] at h_nonempty
      by_cases h_len : s.length = 0
      · simp [h_len] at h_nonempty
      · simp [h_len] at h_nonempty
        by_cases h_find : find_first_word_with_consonants (s.splitOn " ") n = none
        · simp [h_find] at h_nonempty
        · simp [h_find] at h_nonempty
          obtain ⟨word, idx⟩ := h_find
          simp at h_nonempty
          constructor
          · sorry
          constructor
          · sorry
          constructor
          · sorry
          · by_cases h_remaining : join_words_from (s.splitOn " ") (idx + 1) = ""
            · simp [h_remaining] at h_nonempty
              simp [h_remaining]
              simp [implementation]
              rw [h_remaining]
              simp
            · simp [h_remaining] at h_nonempty
              simp [h_remaining]
              sorry

-- LLM HELPER
lemma count_consonants_eq (word: String) : count_consonants word = (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  unfold count_consonants
  congr 1
  ext c
  simp [is_consonant]