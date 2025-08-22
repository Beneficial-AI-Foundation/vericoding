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
        simp [implementation]
        split_ifs with h_len
        · rfl
        · simp at h_len
          let words := s.splitOn " "
          cases h_find : find_first_word_with_n_consonants words n with
          | none => rfl
          | some pair => simp
      · intro h_or
        simp [implementation]
        cases h_or with
        | inl h_len => simp [h_len]
        | inr h_all =>
          split_ifs with h_len_zero
          · rfl
          · simp at h_len_zero
            let words := s.splitOn " "
            cases h_find : find_first_word_with_n_consonants words n with
            | none => rfl
            | some pair =>
              obtain ⟨first_word, idx⟩ := pair
              simp
              exfalso
              have h_exists : ∃ w, w ∈ words ∧ count_consonants w = n := by
                induction words generalizing idx with
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
              have h_not_all : ¬words.all (fun word => count_consonants word ≠ n) := by
                simp [List.all_eq_true]
                use w
                simp [h_w_mem, h_w_count]
              have h_all_conv : words.all (fun word => (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length ≠ n) = words.all (fun word => count_consonants word ≠ n) := by
                simp [count_consonants, is_consonant]
              rw [h_all_conv] at h_all
              exact h_not_all h_all
    · intro h_pos
      simp [implementation] at h_pos
      split_ifs at h_pos with h_len
      · simp at h_pos
      · simp at h_len
        let words := s.splitOn " "
        cases h_find : find_first_word_with_n_consonants words n with
        | none => simp at h_pos
        | some pair =>
          obtain ⟨first_word, idx⟩ := pair
          simp [implementation] at h_pos
          simp [h_len, h_find] at h_pos
          simp [List.get_cons_zero, List.tail_cons]
          constructor
          · have h_mem : first_word ∈ words := by
              induction words generalizing idx with
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
            exact h_mem
          · constructor
            · have h_count : count_consonants first_word = n := by
                induction words generalizing idx with
                | nil => simp [find_first_word_with_n_consonants] at h_find
                | cons hd tl ih =>
                  simp [find_first_word_with_n_consonants] at h_find
                  split_ifs at h_find with h_hd
                  · simp at h_find
                    rw [h_find.1]
                    exact h_hd
                  · cases h' : find_first_word_with_n_consonants tl n with
                    | none => simp [h'] at h_find
                    | some p =>
                      obtain ⟨w', i'⟩ := p
                      simp [h'] at h_find
                      exact ih h_find.1
              convert count_consonants_eq first_word
              simp [count_consonants, is_consonant] at h_count
              exact h_count
            · constructor
              · intro i h_i_lt
                simp
                have h_idx_eq : idx = words.idxOf first_word := by
                  induction words generalizing idx with
                  | nil => simp [find_first_word_with_n_consonants] at h_find
                  | cons hd tl ih =>
                    simp [find_first_word_with_n_consonants] at h_find
                    split_ifs at h_find with h_hd
                    · simp at h_find
                      simp [List.idxOf, h_find.1]
                    · cases h' : find_first_word_with_n_consonants tl n with
                      | none => simp [h'] at h_find
                      | some p =>
                        obtain ⟨w', i'⟩ := p
                        simp [h'] at h_find
                        simp [List.idxOf]
                        split_ifs with h_eq
                        · rw [h_eq] at h_hd
                          have : count_consonants first_word = n := by
                            induction tl generalizing i' with
                            | nil => simp [find_first_word_with_n_consonants] at h'
                            | cons hd2 tl2 ih2 =>
                              simp [find_first_word_with_n_consonants] at h'
                              split_ifs at h' with h_hd2
                              · simp at h'
                                rw [h'.1, h_find.1]
                                exact h_hd2
                              · cases h'' : find_first_word_with_n_consonants tl2 n with
                                | none => simp [h''] at h'
                                | some p2 =>
                                  obtain ⟨w2, i2⟩ := p2
                                  simp [h''] at h'
                                  exact ih2 h'.1
                          rw [h_eq] at this
                          exact absurd this h_hd
                        · simp [ih h_find.1]
                rw [h_idx_eq] at h_i_lt
                by_contra h_contra
                simp at h_contra
                have h_ne : words[i]! ≠ first_word := List.get_ne_of_lt_idxOf h_i_lt
                have h_count_i : count_consonants (words[i]!) = n := by
                  simp [count_consonants, is_consonant] at h_contra
                  exact h_contra
                have h_first_is_first : ∀ j, j < words.idxOf first_word → count_consonants (words[j]!) ≠ n := by
                  intro j h_j_lt
                  induction words generalizing idx with
                  | nil => simp [find_first_word_with_n_consonants] at h_find
                  | cons hd tl ih =>
                    simp [find_first_word_with_n_consonants] at h_find
                    split_ifs at h_find with h_hd
                    · simp at h_find
                      simp [List.idxOf, h_find.1] at h_j_lt
                      exact Nat.lt_irrefl 0 h_j_lt
                    · cases h' : find_first_word_with_n_consonants tl n with
                      | none => simp [h'] at h_find
                      | some p =>
                        obtain ⟨w', i'⟩ := p
                        simp [h'] at h_find
                        simp [List.idxOf] at h_j_lt
                        split_ifs at h_j_lt with h_eq
                        · rw [h_eq] at h_hd
                          rw [h_find.1] at h_eq
                          have : count_consonants first_word = n := by
                            induction tl generalizing i' with
                            | nil => simp [find_first_word_with_n_consonants] at h'
                            | cons hd2 tl2 ih2 =>
                              simp [find_first_word_with_n_consonants] at h'
                              split_ifs at h' with h_hd2
                              · simp at h'
                                rw [h'.1]
                                exact h_hd2
                              · cases h'' : find_first_word_with_n_consonants tl2 n with
                                | none => simp [h''] at h'
                                | some p2 =>
                                  obtain ⟨w2, i2⟩ := p2
                                  simp [h''] at h'
                                  exact ih2 h'.1
                          rw [h_eq] at this
                          exact absurd this h_hd
                        · cases j with
                          | zero => exact h_hd
                          | succ j' =>
                            have : j' < tl.idxOf first_word := Nat.lt_of_succ_lt_succ h_j_lt
                            have : count_consonants (tl[j']!) ≠ n := ih h_find.1 j' this
                            simp [List.get_cons_succ]
                            exact this
                exact h_first_is_first i h_i_lt h_count_i
              · simp [List.foldl_eq_foldl_of_ne_nil]
                rfl