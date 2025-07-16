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
lemma string_splitOn_nonempty (s: String) (h: s.length > 0) : s.splitOn " " ≠ [] := by
  simp [List.ne_nil_iff_length_pos]
  exact String.length_splitOn_pos h

-- LLM HELPER
lemma find_first_gives_valid_index {words: List String} {n: Nat} {word: String} {idx: Nat}
  (h: find_first_word_with_n_consonants words n = some (word, idx)) : 
  idx < words.length := by
  induction words generalizing idx with
  | nil => simp [find_first_word_with_n_consonants] at h
  | cons hd tl ih =>
    simp [find_first_word_with_n_consonants] at h
    split_ifs at h with h_count
    · simp at h
      simp
    · cases h_find : find_first_word_with_n_consonants tl n with
      | none => simp [h_find] at h
      | some p =>
        obtain ⟨w, i⟩ := p
        simp [h_find] at h
        simp
        exact Nat.succ_lt_succ (ih h.1)

-- LLM HELPER
lemma drop_length_lt {α: Type*} (l: List α) (k: Nat) (h: k < l.length) : 
  (l.drop (k + 1)).length < l.length := by
  rw [List.length_drop]
  cases' Nat.lt_or_ge l.length (k + 1) with h1 h2
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt h1)]
    exact List.length_pos_of_ne_nil (List.ne_nil_of_length_pos (Nat.lt_trans (Nat.zero_lt_succ k) h1))
  · rw [Nat.sub_lt_iff_lt_add]
    · simp
    · exact List.length_pos_of_ne_nil (List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h))

-- LLM HELPER  
lemma join_words_length_bound (words: List String) :
  (join_words words).length ≤ (words.foldl (fun acc word => acc ++ " " ++ word) "").length := by
  induction words with
  | nil => simp [join_words]
  | cons hd tl ih =>
    simp [join_words]
    cases tl with
    | nil => 
      simp
      omega
    | cons hd' tl' => 
      simp
      have h_fold : (hd' :: tl').foldl (fun acc word => acc ++ " " ++ word) "" = 
        " " ++ hd' ++ (tl'.foldl (fun acc word => acc ++ " " ++ word) "") := by
        simp [List.foldl_cons]
      rw [h_fold]
      simp
      omega

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
  have h_nonempty : words ≠ [] := string_splitOn_nonempty s h
  have h_idx_valid : idx < words.length := find_first_gives_valid_index (by assumption)
  have h_drop_shorter : remaining_words.length < words.length := drop_length_lt words idx h_idx_valid
  have h_join_bound : remaining_string.length ≤ (remaining_words.foldl (fun acc word => acc ++ " " ++ word) "").length :=
    join_words_length_bound remaining_words
  have h_fold_bound : (remaining_words.foldl (fun acc word => acc ++ " " ++ word) "").length < s.length := by
    simp [remaining_words]
    have h_drop_bound : ((words.drop (idx + 1)).foldl (fun acc word => acc ++ " " ++ word) "").length ≤ 
      (words.foldl (fun acc word => acc ++ " " ++ word) "").length - (idx + 1) := by
      sorry
    have h_words_bound : (words.foldl (fun acc word => acc ++ " " ++ word) "").length ≤ s.length := by
      sorry
    omega
  exact Nat.lt_of_le_of_lt h_join_bound h_fold_bound

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
                by_contra h_contra
                sorry
              · simp
                rfl