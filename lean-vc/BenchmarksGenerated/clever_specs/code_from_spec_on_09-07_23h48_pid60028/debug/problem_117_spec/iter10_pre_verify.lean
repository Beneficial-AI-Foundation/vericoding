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
    let first_word_idx := words.idxOf first_word
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
def find_first_word_with_n_consonants (words: List String) (n: Nat) : Option (String × Nat) :=
  match words with
  | [] => none
  | word :: rest =>
    if count_consonants word = n then
      some (word, 0)
    else
      match find_first_word_with_n_consonants rest n with
      | none => none
      | some (found_word, idx) => some (found_word, idx + 1)

-- LLM HELPER
def join_words (words: List String) : String :=
  match words with
  | [] => ""
  | [word] => word
  | word :: rest => word ++ " " ++ join_words rest

def implementation (s: String) (n: Nat) : List String :=
  if s.length = 0 then
    []
  else
    let words := s.splitOn " "
    match find_first_word_with_n_consonants words n with
    | none => []
    | some (first_word, idx) =>
      let remaining_words := words.drop (idx + 1)
      let remaining_string := join_words remaining_words
      first_word :: implementation remaining_string n
termination_by s.length

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n := by
  simp [problem_spec]
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
          · simp at h_len
            cases h_find : find_first_word_with_n_consonants (s.splitOn " ") n with
            | none => rfl
            | some pair =>
              simp
              exfalso
              obtain ⟨first_word, idx⟩ := pair
              have h_exists : ∃ w, w ∈ s.splitOn " " ∧ count_consonants w = n := by
                induction s.splitOn " " generalizing idx with
                | nil => simp [find_first_word_with_n_consonants] at h_find
                | cons hd tl ih =>
                  simp [find_first_word_with_n_consonants] at h_find
                  split_ifs at h_find with h_hd
                  · simp at h_find
                    use hd
                    simp [h_find.1, h_hd]
                  · cases h' : find_first_word_with_n_consonants tl n with
                    | none => simp [h'] at h_find
                    | some p =>
                      obtain ⟨w', i'⟩ := p
                      simp [h'] at h_find
                      obtain ⟨w, h_w_mem, h_w_count⟩ := ih h_find.1
                      use w
                      simp [h_w_mem, h_w_count]
              obtain ⟨w, h_w_mem, h_w_count⟩ := h_exists
              have h_not_all : ¬(s.splitOn " ").all (fun word => count_consonants word ≠ n) := by
                simp [List.all_eq_true]
                use w
                simp [h_w_mem, h_w_count]
              simp [count_consonants, is_consonant] at h_all
              exact h_not_all h_all
      · intro h_impl_empty
        simp [implementation] at h_impl_empty
        split_ifs at h_impl_empty with h_len
        · left
          exact h_len
        · right
          simp at h_len
          cases h_find : find_first_word_with_n_consonants (s.splitOn " ") n with
          | none =>
            simp [count_consonants, is_consonant]
            induction s.splitOn " " with
            | nil => simp
            | cons hd tl ih =>
              simp [find_first_word_with_n_consonants] at h_find
              split_ifs at h_find with h_hd
              · simp at h_find
              · cases h' : find_first_word_with_n_consonants tl n with
                | none =>
                  simp [h'] at h_find
                  simp [List.all_cons]
                  exact ⟨h_hd, ih h_find⟩
                | some p => simp [h'] at h_find
          | some pair =>
            simp at h_impl_empty
    · intro h_pos
      simp [implementation] at h_pos
      split_ifs at h_pos with h_len
      · simp at h_pos
      · simp at h_len
        cases h_find : find_first_word_with_n_consonants (s.splitOn " ") n with
        | none => simp at h_pos
        | some pair =>
          obtain ⟨first_word, idx⟩ := pair
          simp at h_pos
          simp
          constructor
          · induction s.splitOn " " generalizing idx with
            | nil => simp [find_first_word_with_n_consonants] at h_find
            | cons hd tl ih =>
              simp [find_first_word_with_n_consonants] at h_find
              split_ifs at h_find with h_hd
              · simp at h_find
                simp [h_find.1]
              · cases h' : find_first_word_with_n_consonants tl n with
                | none => simp [h'] at h_find
                | some p =>
                  obtain ⟨w', i'⟩ := p
                  simp [h'] at h_find
                  simp [ih h_find.1]
          · constructor
            · induction s.splitOn " " generalizing idx with
              | nil => simp [find_first_word_with_n_consonants] at h_find
              | cons hd tl ih =>
                simp [find_first_word_with_n_consonants] at h_find
                split_ifs at h_find with h_hd
                · simp at h_find
                  rw [h_find.1]
                  simp [count_consonants, is_consonant]
                  exact h_hd
                · cases h' : find_first_word_with_n_consonants tl n with
                  | none => simp [h'] at h_find
                  | some p =>
                    obtain ⟨w', i'⟩ := p
                    simp [h'] at h_find
                    exact ih h_find.1
            · constructor
              · intro i h_i_lt
                by_contra h_contra
                induction s.splitOn " " generalizing idx with
                | nil => simp [find_first_word_with_n_consonants] at h_find
                | cons hd tl ih =>
                  simp [find_first_word_with_n_consonants] at h_find
                  split_ifs at h_find with h_hd
                  · simp at h_find
                    simp [h_find.1] at h_i_lt
                    simp at h_i_lt
                  · cases h' : find_first_word_with_n_consonants tl n with
                    | none => simp [h'] at h_find
                    | some p =>
                      obtain ⟨w', i'⟩ := p
                      simp [h'] at h_find
                      simp [List.idxOf_cons] at h_i_lt h_contra
                      split_ifs at h_i_lt h_contra with h_eq
                      · simp at h_i_lt
                      · cases i with
                        | zero => 
                          simp at h_contra
                          exact h_hd h_contra
                        | succ i' =>
                          simp at h_i_lt h_contra
                          exact ih h_find.1 i' h_i_lt h_contra
              · simp [List.tail_cons]
                rfl