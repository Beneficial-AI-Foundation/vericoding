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

def implementation (s: String) (n: Nat) : List String :=
  if s.length = 0 then []
  else
    let words := s.splitOn " "
    match find_first_word_with_consonants words n with
    | none => []
    | some (first_word, idx) =>
      let remaining_string := join_words_from words (idx + 1)
      first_word :: implementation remaining_string n
termination_by implementation s n => s.length

-- LLM HELPER
lemma is_consonant_eq (c: Char) : (is_consonant c = true) ↔ (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha = true) := by
  unfold is_consonant
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

-- LLM HELPER
lemma count_consonants_eq (word: String) : count_consonants word = (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  unfold count_consonants
  congr 1
  ext c
  simp [is_consonant]

-- LLM HELPER
lemma find_first_word_properties (words: List String) (n: Nat) (word: String) (idx: Nat) :
  find_first_word_with_consonants words n = some (word, idx) →
  word ∈ words ∧ count_consonants word = n ∧ idx < words.length ∧ words[idx]! = word ∧
  (∀ i, i < idx → count_consonants (words[i]!) ≠ n) := by
  intro h
  induction words generalizing idx with
  | nil => simp [find_first_word_with_consonants] at h
  | cons head tail ih =>
    simp [find_first_word_with_consonants] at h
    split_ifs at h with h_cond
    · simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      constructor
      · simp
      constructor
      · exact h_cond
      constructor
      · simp
      constructor
      · simp
      · intro i hi
        simp at hi
    · cases h_rec : find_first_word_with_consonants tail n with
      | none => simp [h_rec] at h
      | some pair =>
        cases pair with
        | mk w i =>
          simp [h_rec] at h
          obtain ⟨h1, h2⟩ := h
          subst h1 h2
          have ih_result := ih h_rec
          obtain ⟨h_mem, h_count, h_len, h_get, h_prev⟩ := ih_result
          constructor
          · simp
            right
            exact h_mem
          constructor
          · exact h_count
          constructor
          · simp
            exact Nat.succ_lt_succ h_len
          constructor
          · simp
            exact h_get
          · intro j hj
            cases j with
            | zero => simp; exact h_cond
            | succ j' =>
              simp at hj
              simp
              apply h_prev
              exact Nat.lt_of_succ_lt_succ hj

-- LLM HELPER
lemma join_words_from_eq (words: List String) (start_idx: Nat) :
  join_words_from words start_idx = 
  (words.drop start_idx).foldl (fun acc word => if acc = "" then word else acc ++ " " ++ word) "" := by
  unfold join_words_from
  cases h : words.drop start_idx with
  | nil => simp
  | cons first rest =>
    simp [h]
    induction rest generalizing first with
    | nil => simp
    | cons head tail ih =>
      simp
      have : first ≠ "" := by
        cases first with
        | mk chars => simp
      simp [this]
      rfl

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
          split_ifs with h_len
          · rfl
          · split_ifs with h_find
            · simp
            · rfl
      · intro h_empty
        simp [implementation] at h_empty
        split_ifs at h_empty with h_len h_find
        · left; exact h_len
        · right
          simp [h_find] at h_empty
          exact h_empty
        · simp at h_empty
    · intro h_nonempty
      simp [implementation] at h_nonempty
      split_ifs at h_nonempty with h_len h_find
      · simp at h_nonempty
      · simp at h_nonempty
      · obtain ⟨word, idx⟩ := h_find
        simp at h_nonempty
        have h_props := find_first_word_properties (s.splitOn " ") n word idx (Eq.refl _)
        obtain ⟨h_mem, h_count, h_idx_bound, h_get, h_prev⟩ := h_props
        simp at h_nonempty
        constructor
        · exact h_mem
        constructor
        · rw [count_consonants_eq] at h_count
          exact h_count
        constructor
        · rw [count_consonants_eq] at h_prev
          exact h_prev
        · simp
          rw [join_words_from_eq]
          rfl