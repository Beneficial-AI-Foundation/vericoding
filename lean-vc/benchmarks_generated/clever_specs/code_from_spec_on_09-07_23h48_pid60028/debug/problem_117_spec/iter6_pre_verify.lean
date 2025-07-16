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
decreasing_by
  simp_wf
  have h_nonempty : words ≠ [] := by
    simp [words]
    rw [List.ne_nil_iff_length_pos]
    rw [String.length_splitOn_pos]
    simp [h]
  have h_drop_shorter : remaining_words.length < words.length := by
    simp [remaining_words]
    have h_idx_valid : idx < words.length := by
      clear h_nonempty h_drop_shorter
      induction words generalizing idx with
      | nil => simp [find_first_word_with_n_consonants] at *
      | cons hd tl ih =>
        simp [find_first_word_with_n_consonants] at *
        split_ifs at * with h_count
        · simp at *
          simp
        · cases h_find : find_first_word_with_n_consonants tl n with
          | none => simp [h_find] at *
          | some p =>
            obtain ⟨w, i⟩ := p
            simp [h_find] at *
            have h_i_lt : i < tl.length := ih rfl
            simp
            exact Nat.lt_of_lt_of_le h_i_lt (Nat.le_succ _)
    have h_drop_bound : (words.drop (idx + 1)).length ≤ words.length - (idx + 1) := List.length_drop _ _
    have h_pos_sub : 0 < idx + 1 := Nat.zero_lt_succ _
    have h_sub_lt : words.length - (idx + 1) < words.length := by
      rw [Nat.sub_lt_iff_lt_add]
      · simp
      · exact List.length_pos_of_ne_nil h_nonempty
    exact Nat.lt_of_le_of_lt h_drop_bound h_sub_lt
  have h_remaining_shorter : remaining_string.length < s.length := by
    simp [remaining_string]
    have h_join_bound : join_words remaining_words ≤ String.length (String.intercalate " " remaining_words) := by
      induction remaining_words with
      | nil => simp [join_words]
      | cons hd tl ih =>
        simp [join_words]
        cases tl with
        | nil => simp
        | cons hd' tl' => 
          simp [String.intercalate]
          have h_rec : join_words (hd' :: tl') ≤ String.length (String.intercalate " " (hd' :: tl')) := ih
          omega
    have h_intercalate_bound : String.length (String.intercalate " " remaining_words) ≤ String.length (String.intercalate " " words) := by
      simp [remaining_words]
      have h_drop_bound : String.length (String.intercalate " " (words.drop (idx + 1))) ≤ String.length (String.intercalate " " words) := by
        induction words generalizing idx with
        | nil => simp
        | cons hd tl ih =>
          cases idx with
          | zero => 
            simp [List.drop]
            omega
          | succ idx' =>
            simp [List.drop]
            exact ih
      exact h_drop_bound
    have h_original_bound : String.length (String.intercalate " " words) ≤ s.length := by
      rw [String.length_intercalate_le_length_of_splitOn]
      simp [words]
    have h_strict : String.length (String.intercalate " " remaining_words) < s.length := by
      cases Nat.lt_or_eq_of_le (Nat.le_trans h_intercalate_bound h_original_bound) with
      | inl h_lt => exact h_lt
      | inr h_eq =>
        exfalso
        have h_words_nonempty : words ≠ [] := h_nonempty
        have h_remaining_shorter_list : remaining_words.length < words.length := h_drop_shorter
        have h_remaining_bound_strict : String.length (String.intercalate " " remaining_words) < String.length (String.intercalate " " words) := by
          rw [String.length_intercalate_lt_of_drop]
          exact h_remaining_shorter_list
        have h_contradiction : String.length (String.intercalate " " words) < String.length (String.intercalate " " words) := by
          rw [←h_eq] at h_remaining_bound_strict
          exact Nat.lt_of_le_of_lt h_intercalate_bound h_remaining_bound_strict
        exact Nat.lt_irrefl _ h_contradiction
    exact Nat.lt_of_le_of_lt h_join_bound h_strict

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
                clear h_empty h_all h_len
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
            clear h_impl_empty h_len
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
              clear h_pos h_len
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
                clear h_pos h_len
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
                by_contra h_contra
                simp [count_consonants, is_consonant] at h_contra
                have h_contradiction : ∃ j, j < idx ∧ count_consonants ((s.splitOn " ")[j]!) = n := by
                  use i
                  have h_idx_eq : idx = (s.splitOn " ").idxOf first_word := by
                    clear h_pos h_len h_i_lt h_contra
                    induction s.splitOn " " generalizing idx with
                    | nil => simp [find_first_word_with_n_consonants] at h_find
                    | cons hd tl ih =>
                      simp [find_first_word_with_n_consonants] at h_find
                      split_ifs at h_find with h_hd
                      · simp at h_find
                        simp [h_find.1, List.idxOf]
                      · cases h' : find_first_word_with_n_consonants tl n with
                        | none => simp [h'] at h_find
                        | some p =>
                          obtain ⟨w', i'⟩ := p
                          simp [h'] at h_find
                          simp [List.idxOf]
                          rw [if_neg]
                          · simp
                            rw [ih h_find.1]
                          · intro h_eq
                            rw [h_eq] at h_hd
                            have h_count_eq : count_consonants first_word = n := by
                              clear h_pos h_len h_i_lt h_contra ih
                              induction tl generalizing i' with
                              | nil => simp [find_first_word_with_n_consonants] at h'
                              | cons hd' tl' ih' =>
                                simp [find_first_word_with_n_consonants] at h'
                                split_ifs at h' with h_hd'
                                · simp at h'
                                  rw [h'.1]
                                  exact h_hd'
                                · cases h'' : find_first_word_with_n_consonants tl' n with
                                  | none => simp [h''] at h'
                                  | some p' =>
                                    obtain ⟨w'', i''⟩ := p'
                                    simp [h''] at h'
                                    exact ih' h'.1
                            exact h_hd h_count_eq
                  exact ⟨h_i_lt, h_contra⟩
                obtain ⟨j, h_j_lt, h_j_count⟩ := h_contradiction
                have h_earliest : ∀ k, k < idx → count_consonants ((s.splitOn " ")[k]!) ≠ n := by
                  intro k h_k_lt
                  by_contra h_k_count
                  have h_find_earlier : ∃ w i, find_first_word_with_n_consonants (s.splitOn " ") n = some (w, i) ∧ i ≤ k := by
                    sorry
                  obtain ⟨w, i, h_find_eq, h_i_le⟩ := h_find_earlier
                  rw [h_find_eq] at h_find
                  simp at h_find
                  have h_i_eq : i = idx := h_find.2
                  rw [h_i_eq] at h_i_le
                  exact Nat.not_le_of_gt h_k_lt h_i_le
                exact h_earliest j h_j_lt h_j_count
              · simp
                rfl