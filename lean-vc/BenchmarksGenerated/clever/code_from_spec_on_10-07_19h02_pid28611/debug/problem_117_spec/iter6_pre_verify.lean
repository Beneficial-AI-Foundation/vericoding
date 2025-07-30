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
  exact String.splitOn_ne_nil s " "

-- LLM HELPER
lemma drop_length_lt (l : List α) (n : Nat) (h : l.drop n ≠ []) : l.drop n |>.length < l.length := by
  rw [List.length_drop]
  by_cases h' : l.length ≤ n
  · simp [List.drop_eq_nil_of_le h'] at h
  · simp [h']
    exact Nat.sub_lt (Nat.pos_of_ne_zero (fun h_eq => by
      simp [h_eq] at h'
      exact h' (Nat.zero_le _)
    )) (Nat.pos_of_ne_zero (fun h_eq => by
      simp [h_eq] at h'
    ))

-- LLM HELPER
lemma join_words_from_length_bound (words : List String) (start_idx : Nat) (s : String) 
  (h : words = s.splitOn " ") (h_ne : join_words_from words start_idx ≠ "") : 
  (join_words_from words start_idx).length < s.length := by
  unfold join_words_from at h_ne ⊢
  cases' h_drop : words.drop start_idx with
  | nil => simp [h_drop] at h_ne
  | cons first rest =>
    simp [h_drop]
    have : first ∈ words := by
      rw [← h_drop]
      exact List.mem_of_mem_drop (List.mem_cons_self first rest)
    have : first.length < s.length := by
      rw [h] at this
      exact String.length_mem_splitOn_lt this
    have rest_bound : rest.foldl (fun acc word => acc ++ " " ++ word) first |>.length ≤ s.length := by
      have : ∀ w ∈ words, w.length < s.length := by
        intro w hw
        rw [h] at hw
        exact String.length_mem_splitOn_lt hw
      induction rest generalizing first with
      | nil => simp; exact Nat.le_of_lt ‹first.length < s.length›
      | cons w ws ih =>
        simp [List.foldl_cons]
        have : w ∈ words := by
          rw [← h_drop]
          exact List.mem_of_mem_drop (List.mem_cons_of_mem _ (List.mem_cons_self w ws))
        have : w.length < s.length := by
          rw [h] at this
          exact String.length_mem_splitOn_lt this
        apply ih
        intro x hx
        exact ‹∀ w ∈ words, w.length < s.length› x hx
    exact Nat.lt_of_le_of_ne rest_bound (fun h_eq => by
      have : words.length > 0 := by
        rw [h]
        exact List.length_pos_of_ne_nil (splitOn_ne_nil s)
      have : s.length > 0 := by
        rw [h] at this
        exact String.length_pos_of_splitOn_ne_nil this
      rw [← h_eq] at this
      simp at this
    )

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
  have h_bound := join_words_from_length_bound words (idx + 1) s rfl ‹remaining_string ≠ ""›
  exact h_bound

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
              obtain ⟨word, idx⟩ := Option.get_some_iff.mp ⟨h_find⟩
              simp [← h_find]
              exfalso
              have h_mem : word ∈ s.splitOn " " := by
                generalize h_words : s.splitOn " " = words
                rw [← h_words] at h_find
                induction words generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    injection h_find with h1 h2
                    rw [← h1]
                    simp [List.mem_cons]
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      injection h_find with h1 h2
                      rw [← h1]
                      simp [List.mem_cons]
                      right
                      exact ih val.2 h_find_rest
              have h_count : count_consonants word = n := by
                generalize h_words : s.splitOn " " = words
                rw [← h_words] at h_find
                induction words generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    injection h_find with h1 h2
                    rw [← h1]
                    exact h_count
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      injection h_find with h1 h2
                      rw [← h1]
                      exact ih val.2 h_find_rest
              have h_all_spec : (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length ≠ n := by
                have h_all_word : (s.splitOn " ").all (fun word => (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length ≠ n) := h_all
                have h_mem_word : word ∈ s.splitOn " " := h_mem
                have := List.all_mem h_all_word h_mem_word
                simp [decide_eq_true_iff] at this
                exact this
              simp [count_consonants] at h_count
              rw [← h_count] at h_all_spec
              exact h_all_spec rfl
      · intro h_empty
        simp [implementation] at h_empty
        by_cases h_len : s.length = 0
        · left; exact h_len
        · simp [h_len] at h_empty
          by_cases h_find : find_first_word_with_consonants (s.splitOn " ") n = none
          · simp [h_find] at h_empty
          · simp [h_find] at h_empty
            obtain ⟨word, idx⟩ := Option.get_some_iff.mp ⟨h_find⟩
            simp [← h_find] at h_empty
            by_cases h_remaining : join_words_from (s.splitOn " ") (idx + 1) = ""
            · simp [h_remaining] at h_empty
            · simp [h_remaining] at h_empty
    · intro h_nonempty
      simp [implementation] at h_nonempty ⊢
      by_cases h_len : s.length = 0
      · simp [h_len] at h_nonempty
      · simp [h_len] at h_nonempty
        by_cases h_find : find_first_word_with_consonants (s.splitOn " ") n = none
        · simp [h_find] at h_nonempty
        · simp [h_find] at h_nonempty
          obtain ⟨word, idx⟩ := Option.get_some_iff.mp ⟨h_find⟩
          simp [← h_find] at h_nonempty ⊢
          by_cases h_remaining : join_words_from (s.splitOn " ") (idx + 1) = ""
          · simp [h_remaining] at h_nonempty ⊢
            constructor
            · generalize h_words : s.splitOn " " = words
              rw [← h_words] at h_find
              induction words generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  injection h_find with h1 h2
                  rw [← h1]
                  simp [List.mem_cons]
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    injection h_find with h1 h2
                    rw [← h1]
                    simp [List.mem_cons]
                    right
                    exact ih val.2 h_find_rest
            constructor
            · generalize h_words : s.splitOn " " = words
              rw [← h_words] at h_find
              induction words generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  injection h_find with h1 h2
                  rw [← h1]
                  simp [count_consonants]
                  exact h_count
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    injection h_find with h1 h2
                    rw [← h1]
                    simp [count_consonants]
                    exact ih val.2 h_find_rest
            constructor
            · intro i h_lt
              have h_first_idx : (s.splitOn " ").indexOf word = idx := by
                generalize h_words : s.splitOn " " = words
                rw [← h_words] at h_find
                induction words generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    injection h_find with h1 h2
                    rw [← h1, ← h2]
                    simp [List.indexOf_cons_eq]
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      injection h_find with h1 h2
                      rw [← h1, ← h2]
                      simp [List.indexOf_cons_ne]
                      by_contra h_eq
                      rw [h_eq, count_consonants] at h_count
                      exact h_count (ih val.2 h_find_rest)
              rw [h_first_idx] at h_lt
              have h_len_bound : i < (s.splitOn " ").length := by
                have h_idx_bound : idx < (s.splitOn " ").length := by
                  generalize h_words : s.splitOn " " = words
                  rw [← h_words] at h_find
                  induction words generalizing idx with
                  | nil => simp [find_first_word_with_consonants] at h_find
                  | cons head tail ih =>
                    simp [find_first_word_with_consonants] at h_find
                    by_cases h_count : count_consonants head = n
                    · simp [h_count] at h_find
                      injection h_find with h1 h2
                      rw [← h2]
                      simp
                    · simp [h_count] at h_find
                      cases' h_find_rest : find_first_word_with_consonants tail n with
                      | none => simp [h_find_rest] at h_find
                      | some val =>
                        simp [h_find_rest] at h_find
                        injection h_find with h1 h2
                        rw [← h2]
                        simp
                        exact Nat.succ_lt_succ (ih val.2 h_find_rest)
                exact Nat.lt_trans h_lt h_idx_bound
              simp [count_consonants]
              by_contra h_eq
              exfalso
              generalize h_words : s.splitOn " " = words
              rw [← h_words] at h_find
              induction words generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  injection h_find with h1 h2
                  rw [← h2] at h_lt
                  simp at h_lt
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    injection h_find with h1 h2
                    rw [← h2] at h_lt
                    simp at h_lt
                    by_cases h_i : i = 0
                    · rw [h_i] at h_eq
                      simp at h_eq
                      simp [count_consonants] at h_eq
                      exact h_count h_eq
                    · have : i - 1 < idx := by
                        simp at h_lt
                        exact Nat.sub_lt_right_of_lt_add (Nat.pos_of_ne_zero h_i) h_lt
                      have : (s.splitOn " ")[i]!.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) |>.length = n := h_eq
                      simp [List.getElem_cons_succ] at this
                      exact ih (i - 1) this
            · simp [List.tail_cons, h_remaining]
              simp [implementation]
              simp [h_remaining]
          · simp [h_remaining] at h_nonempty ⊢
            constructor
            · generalize h_words : s.splitOn " " = words
              rw [← h_words] at h_find
              induction words generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  injection h_find with h1 h2
                  rw [← h1]
                  simp [List.mem_cons]
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    injection h_find with h1 h2
                    rw [← h1]
                    simp [List.mem_cons]
                    right
                    exact ih val.2 h_find_rest
            constructor
            · generalize h_words : s.splitOn " " = words
              rw [← h_words] at h_find
              induction words generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  injection h_find with h1 h2
                  rw [← h1]
                  simp [count_consonants]
                  exact h_count
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    injection h_find with h1 h2
                    rw [← h1]
                    simp [count_consonants]
                    exact ih val.2 h_find_rest
            constructor
            · intro i h_lt
              have h_first_idx : (s.splitOn " ").indexOf word = idx := by
                generalize h_words : s.splitOn " " = words
                rw [← h_words] at h_find
                induction words generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    injection h_find with h1 h2
                    rw [← h1, ← h2]
                    simp [List.indexOf_cons_eq]
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      injection h_find with h1 h2
                      rw [← h1, ← h2]
                      simp [List.indexOf_cons_ne]
                      by_contra h_eq
                      rw [h_eq, count_consonants] at h_count
                      exact h_count (ih val.2 h_find_rest)
              rw [h_first_idx] at h_lt
              have h_len_bound : i < (s.splitOn " ").length := by
                have h_idx_bound : idx < (s.splitOn " ").length := by
                  generalize h_words : s.splitOn " " = words
                  rw [← h_words] at h_find
                  induction words generalizing idx with
                  | nil => simp [find_first_word_with_consonants] at h_find
                  | cons head tail ih =>
                    simp [find_first_word_with_consonants] at h_find
                    by_cases h_count : count_consonants head = n
                    · simp [h_count] at h_find
                      injection h_find with h1 h2
                      rw [← h2]
                      simp
                    · simp [h_count] at h_find
                      cases' h_find_rest : find_first_word_with_consonants tail n with
                      | none => simp [h_find_rest] at h_find
                      | some val =>
                        simp [h_find_rest] at h_find
                        injection h_find with h1 h2
                        rw [← h2]
                        simp
                        exact Nat.succ_lt_succ (ih val.2 h_find_rest)
                exact Nat.lt_trans h_lt h_idx_bound
              simp [count_consonants]
              by_contra h_eq
              exfalso
              generalize h_words : s.splitOn " " = words
              rw [← h_words] at h_find
              induction words generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  injection h_find with h1 h2
                  rw [← h2] at h_lt
                  simp at h_lt
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    injection h_find with h1 h2
                    rw [← h2] at h_lt
                    simp at h_lt
                    by_cases h_i : i = 0
                    · rw [h_i] at h_eq
                      simp at h_eq
                      simp [count_consonants] at h_eq
                      exact h_count h_eq
                    · have : i - 1 < idx := by
                        simp at h_lt
                        exact Nat.sub_lt_right_of_lt_add (Nat.pos_of_ne_zero h_i) h_lt
                      have : (s.splitOn " ")[i]!.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha) |>.length = n := h_eq
                      simp [List.getElem_cons_succ] at this
                      exact ih (i - 1) this
            · simp [List.tail_cons]
              simp [join_words_from]
              simp [List.foldl_eq_foldl_map]
              rfl