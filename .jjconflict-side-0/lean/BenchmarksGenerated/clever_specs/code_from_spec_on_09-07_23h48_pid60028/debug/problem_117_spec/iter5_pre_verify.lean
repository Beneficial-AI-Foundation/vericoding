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

-- LLM HELPER
lemma join_words_length_le (words: List String) : join_words words ≤ words.foldl (fun acc word => acc ++ " " ++ word) "" := by
  induction words with
  | nil => simp [join_words]
  | cons hd tl ih =>
    simp [join_words]
    split_ifs
    · simp
    · simp [List.foldl_cons]
      sorry

-- LLM HELPER
lemma join_words_shorter (words: List String) (h: words ≠ []) : 
  join_words words.length < (words.foldl (fun acc word => acc ++ " " ++ word) "").length + 1 := by
  sorry

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
decreasing_by
  simp_wf
  have h_words_nonempty : words ≠ [] := by
    simp [words]
    have h_splitOn_ne_nil : s.splitOn " " ≠ [] := String.splitOn_ne_nil s " "
    exact h_splitOn_ne_nil
  have h_drop_shorter : remaining_words.length < words.length := by
    simp [remaining_words]
    have h_idx_lt : idx < words.length := by
      induction words generalizing idx with
      | nil => 
        simp [find_first_word_with_n_consonants] at *
      | cons hd tl ih =>
        simp [find_first_word_with_n_consonants] at *
        split_ifs at * with h_count
        · simp at *
          simp [Nat.zero_lt_succ]
        · cases h_find : find_first_word_with_n_consonants tl n with
          | none => simp [h_find] at *
          | some p =>
            obtain ⟨w, i⟩ := p
            simp [h_find] at *
            have h_i_lt : i < tl.length := ih rfl
            simp [Nat.succ_lt_succ_iff]
            exact h_i_lt
    have h_drop_lt : (words.drop (idx + 1)).length ≤ words.length - (idx + 1) := List.length_drop _ _
    have h_pos : idx + 1 ≤ words.length := Nat.succ_le_of_lt h_idx_lt
    have h_sub_lt : words.length - (idx + 1) < words.length := 
      Nat.sub_lt (List.length_pos_of_ne_nil h_words_nonempty) (Nat.zero_lt_succ _)
    exact Nat.lt_of_le_of_lt h_drop_lt h_sub_lt
  have h_join_bound : remaining_string.length ≤ remaining_words.foldl (fun acc word => acc.length + 1 + word.length) 0 := by
    simp [remaining_string]
    induction remaining_words with
    | nil => simp [join_words]
    | cons hd tl ih =>
      simp [join_words]
      split_ifs with h_tl
      · simp [h_tl]
      · simp
        have h_rec : join_words tl ≤ tl.foldl (fun acc word => acc.length + 1 + word.length) 0 := by
          exact ih
        omega
  have h_words_bound : words.foldl (fun acc word => acc.length + word.length) 0 ≤ s.length := by
    have h_splitOn_bound : (s.splitOn " ").foldl (fun acc word => acc.length + word.length) 0 ≤ s.length := by
      have h_join_eq : (s.splitOn " ").foldl (fun acc word => acc ++ word) "" = s.replace " " "" := by
        sorry
      have h_len_le : s.replace " " "" ≤ s.length := by
        sorry
      sorry
    exact h_splitOn_bound
  have h_remaining_bound : remaining_words.foldl (fun acc word => acc.length + word.length) 0 < s.length := by
    have h_drop_bound : remaining_words.foldl (fun acc word => acc.length + word.length) 0 ≤ 
      words.foldl (fun acc word => acc.length + word.length) 0 := by
      simp [remaining_words]
      sorry
    have h_strict : remaining_words.foldl (fun acc word => acc.length + word.length) 0 < 
      words.foldl (fun acc word => acc.length + word.length) 0 := by
      simp [remaining_words]
      have h_first_word_pos : first_word.length > 0 := by
        have h_in_words : first_word ∈ words := by
          induction words generalizing idx with
          | nil => simp [find_first_word_with_n_consonants] at *
          | cons hd tl ih =>
            simp [find_first_word_with_n_consonants] at *
            split_ifs at * with h_count
            · simp at *
              simp [*, List.mem_cons]
            · cases h_find : find_first_word_with_n_consonants tl n with
              | none => simp [h_find] at *
              | some p =>
                obtain ⟨w, i⟩ := p
                simp [h_find] at *
                simp [List.mem_cons]
                right
                exact ih rfl
        have h_consonants_pos : count_consonants first_word = n := by
          induction words generalizing idx with
          | nil => simp [find_first_word_with_n_consonants] at *
          | cons hd tl ih =>
            simp [find_first_word_with_n_consonants] at *
            split_ifs at * with h_count
            · simp at *
              exact h_count
            · cases h_find : find_first_word_with_n_consonants tl n with
              | none => simp [h_find] at *
              | some p =>
                obtain ⟨w, i⟩ := p
                simp [h_find] at *
                exact ih rfl
        have h_n_pos : n > 0 := by
          rw [←h_consonants_pos]
          simp [count_consonants]
          have h_exists : ∃ c, c ∈ first_word.data ∧ is_consonant c := by
            by_contra h_not
            simp at h_not
            have h_zero : count_consonants first_word = 0 := by
              simp [count_consonants, List.filter_eq_nil]
              exact h_not
            rw [h_zero] at h_consonants_pos
            rw [h_consonants_pos] at h_n_pos
            exact Nat.lt_irrefl 0 h_n_pos
          obtain ⟨c, h_c_mem, h_c_consonant⟩ := h_exists
          have h_filter_ne_nil : (first_word.data.filter (fun c => is_consonant c)) ≠ [] := by
            simp [List.filter_ne_nil]
            exact ⟨c, h_c_mem, h_c_consonant⟩
          exact List.length_pos_of_ne_nil h_filter_ne_nil
        have h_alpha_pos : first_word.data.any (fun c => c.isAlpha) := by
          have h_consonant_exists : ∃ c, c ∈ first_word.data ∧ is_consonant c := by
            by_contra h_not
            simp at h_not
            have h_zero : count_consonants first_word = 0 := by
              simp [count_consonants, List.filter_eq_nil]
              exact h_not
            rw [h_zero] at h_consonants_pos
            rw [h_consonants_pos] at h_n_pos
            exact Nat.lt_irrefl 0 h_n_pos
          obtain ⟨c, h_c_mem, h_c_consonant⟩ := h_consonant_exists
          simp [List.any_eq_true]
          use c
          exact ⟨h_c_mem, h_c_consonant.right.right⟩
        have h_data_ne_nil : first_word.data ≠ [] := by
          by_contra h_nil
          simp [List.any_eq_true] at h_alpha_pos
          obtain ⟨c, h_c_mem, h_c_alpha⟩ := h_alpha_pos
          rw [h_nil] at h_c_mem
          exact h_c_mem
        exact List.length_pos_of_ne_nil h_data_ne_nil
      sorry
    exact Nat.lt_of_lt_of_le h_strict h_words_bound
  omega

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
          · have h_mem : first_word ∈ s.splitOn " " := by
              induction s.splitOn " " generalizing idx with
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
                induction s.splitOn " " generalizing idx with
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
              simp [count_consonants, is_consonant] at h_count
              exact h_count
            · constructor
              · intro i h_i_lt
                have h_idx_eq : idx = (s.splitOn " ").idxOf first_word := by
                  sorry
                rw [h_idx_eq] at h_i_lt
                by_contra h_contra
                simp [count_consonants, is_consonant] at h_contra
                have h_first_earliest : ∀ j, j < (s.splitOn " ").idxOf first_word → count_consonants ((s.splitOn " ")[j]!) ≠ n := by
                  sorry
                exact h_first_earliest i h_i_lt h_contra
              · simp
                rfl