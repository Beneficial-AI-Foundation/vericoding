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
def string_measure (s: String) : Nat :=
  s.length

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
termination_by string_measure s

-- LLM HELPER
lemma is_consonant_eq (c: Char) : is_consonant c = (c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) := by
  rfl

-- LLM HELPER
lemma count_consonants_eq (word: String) : count_consonants word = (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  simp [count_consonants, is_consonant]

-- LLM HELPER
lemma find_first_word_some_iff (words: List String) (n: Nat) :
  (∃ word idx, find_first_word_with_n_consonants words n = some (word, idx)) ↔
  (∃ word, word ∈ words ∧ count_consonants word = n) := by
  constructor
  · intro ⟨word, idx, h⟩
    use word
    constructor
    · induction words generalizing idx with
      | nil => simp [find_first_word_with_n_consonants] at h
      | cons hd tl ih =>
        simp [find_first_word_with_n_consonants] at h
        split_ifs at h
        · simp at h
          rw [h.1]
          simp
        · cases h' : find_first_word_with_n_consonants tl n with
          | none => simp [h'] at h
          | some pair =>
            obtain ⟨w, i⟩ := pair
            simp [h'] at h
            simp [h.1, h.2]
            right
            exact ih h.1
    · induction words generalizing idx with
      | nil => simp [find_first_word_with_n_consonants] at h
      | cons hd tl ih =>
        simp [find_first_word_with_n_consonants] at h
        split_ifs at h
        · simp at h
          rw [h.1]
          assumption
        · cases h' : find_first_word_with_n_consonants tl n with
          | none => simp [h'] at h
          | some pair =>
            obtain ⟨w, i⟩ := pair
            simp [h'] at h
            exact ih h.1
  · intro ⟨word, h_mem, h_count⟩
    induction words with
    | nil => simp at h_mem
    | cons hd tl ih =>
      simp [find_first_word_with_n_consonants]
      split_ifs with h_hd
      · use hd, 0
        simp
      · cases h_mem with
        | inl h_eq =>
          rw [h_eq] at h_hd
          exact absurd h_count h_hd
        | inr h_tail =>
          obtain ⟨w, i, h_find⟩ := ih ⟨word, h_tail, h_count⟩
          use w, i + 1
          simp [h_find]

-- LLM HELPER
lemma find_first_word_none_iff (words: List String) (n: Nat) :
  find_first_word_with_n_consonants words n = none ↔
  words.all (fun word => count_consonants word ≠ n) := by
  constructor
  · intro h
    induction words with
    | nil => simp
    | cons hd tl ih =>
      simp [find_first_word_with_n_consonants] at h
      split_ifs at h with h_hd
      · simp at h
      · simp
        constructor
        · exact h_hd
        · exact ih h
  · intro h
    induction words with
    | nil => simp [find_first_word_with_n_consonants]
    | cons hd tl ih =>
      simp [find_first_word_with_n_consonants]
      simp at h
      split_ifs with h_hd
      · exact absurd h_hd h.1
      · exact ih h.2

-- LLM HELPER
lemma join_words_foldl (words: List String) :
  join_words words = words.foldl (fun acc word => if acc = "" then word else acc ++ " " ++ word) "" := by
  induction words with
  | nil => simp [join_words]
  | cons hd tl ih =>
    simp [join_words]
    cases tl with
    | nil => simp
    | cons hd2 tl2 =>
      simp [join_words] at ih
      simp [List.foldl_cons]
      rw [ih]
      simp

theorem correctness
(s: String)
(n: Nat)
: problem_spec implementation s n := by
  simp [problem_spec]
  use implementation s n
  constructor
  · rfl
  · intro h_valid
    simp [implementation]
    split_ifs with h_empty
    · simp [h_empty]
      left
      exact h_empty
    · simp [h_empty]
      let words := s.splitOn " "
      cases h_find : find_first_word_with_n_consonants words n with
      | none =>
        simp
        right
        rw [find_first_word_none_iff] at h_find
        convert h_find
        ext word
        simp [count_consonants_eq]
      | some pair =>
        obtain ⟨first_word, idx⟩ := pair
        simp
        constructor
        · simp [List.length_cons]
        · intro h_pos
          simp [List.get_cons_zero, List.tail_cons]
          constructor
          · have h_mem : ∃ w, w ∈ words ∧ count_consonants w = n := by
              rw [← find_first_word_some_iff]
              use first_word, idx
              exact h_find
            obtain ⟨w, h_w_mem, h_w_count⟩ := h_mem
            have h_first_eq : first_word = w := by
              simp [find_first_word_with_n_consonants] at h_find
              induction words generalizing idx with
              | nil => simp at h_find
              | cons hd tl ih =>
                simp at h_find
                split_ifs at h_find with h_hd
                · simp at h_find
                  rw [h_find.1]
                  have : hd ∈ words := by simp [words]
                  have : count_consonants hd = n := h_hd
                  exact hd
                · cases h' : find_first_word_with_n_consonants tl n with
                  | none => simp [h'] at h_find
                  | some p =>
                    obtain ⟨w', i'⟩ := p
                    simp [h'] at h_find
                    exact h_find.1
            rw [h_first_eq]
            exact h_w_mem
          · constructor
            · convert count_consonants_eq first_word
              have h_mem : ∃ w, w ∈ words ∧ count_consonants w = n := by
                rw [← find_first_word_some_iff]
                use first_word, idx
                exact h_find
              obtain ⟨w, h_w_mem, h_w_count⟩ := h_mem
              have h_first_eq : first_word = w := by
                simp [find_first_word_with_n_consonants] at h_find
                induction words generalizing idx with
                | nil => simp at h_find
                | cons hd tl ih =>
                  simp at h_find
                  split_ifs at h_find with h_hd
                  · simp at h_find
                    exact h_find.1
                  · cases h' : find_first_word_with_n_consonants tl n with
                    | none => simp [h'] at h_find
                    | some p =>
                      obtain ⟨w', i'⟩ := p
                      simp [h'] at h_find
                      exact h_find.1
              rw [h_first_eq]
              exact h_w_count
            · constructor
              · intro i h_i_lt
                simp [count_consonants_eq]
                have : idx = words.idxOf first_word := by
                  simp [find_first_word_with_n_consonants] at h_find
                  induction words generalizing idx with
                  | nil => simp at h_find
                  | cons hd tl ih =>
                    simp at h_find
                    split_ifs at h_find with h_hd
                    · simp at h_find
                      rw [h_find.1]
                      simp [List.idxOf]
                      split_ifs
                      · rfl
                      · exfalso
                        exact h ‹hd = first_word›
                    · cases h' : find_first_word_with_n_consonants tl n with
                      | none => simp [h'] at h_find
                      | some p =>
                        obtain ⟨w', i'⟩ := p
                        simp [h'] at h_find
                        have : i' = tl.idxOf first_word := by
                          exact ih h_find.1
                        simp [List.idxOf]
                        split_ifs with h_eq
                        · rw [h_eq] at h_hd
                          exact absurd count_consonants_eq h_hd
                        · simp [this]
                          exact Nat.succ_inj.mpr this
                rw [this] at h_i_lt
                have : i < words.idxOf first_word := h_i_lt
                have : words[i]! ≠ first_word := List.get_ne_of_lt_idxOf this
                by_contra h_contra
                simp at h_contra
                have : count_consonants (words[i]!) = n := h_contra
                have : words[i]! = first_word := by
                  simp [find_first_word_with_n_consonants] at h_find
                  induction words generalizing idx with
                  | nil => simp at h_find
                  | cons hd tl ih =>
                    simp at h_find
                    split_ifs at h_find with h_hd
                    · simp at h_find
                      rw [h_find.1]
                      have : i = 0 := by
                        rw [this] at h_i_lt
                        simp [List.idxOf] at h_i_lt
                        split_ifs at h_i_lt
                        · exact Nat.lt_irrefl 0 h_i_lt
                        · exact Nat.not_lt_zero i h_i_lt
                      simp [this]
                    · cases h' : find_first_word_with_n_consonants tl n with
                      | none => simp [h'] at h_find
                      | some p =>
                        obtain ⟨w', i'⟩ := p
                        simp [h'] at h_find
                        exact h_find.1
                exact absurd this ‹words[i]! ≠ first_word›
              · rfl