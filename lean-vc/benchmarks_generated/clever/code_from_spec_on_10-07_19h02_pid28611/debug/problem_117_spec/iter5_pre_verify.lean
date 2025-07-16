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
    have h_pos : 0 < words.length := by
      simp [words]
      rw [List.length_pos_iff_exists_mem]
      exists ""
      simp [String.splitOn_ne_nil]
    have h_drop_len : (words.drop (idx + 1)).length < words.length := by
      apply List.length_drop_lt_length_of_ne_nil h_ne
      simp [words]
      rw [List.length_pos_iff_exists_mem]
      exists ""
      simp [String.splitOn_ne_nil]
    have h_bound : (match words.drop (idx + 1) with
      | [] => ""
      | first :: rest => rest.foldl (fun acc word => acc ++ " " ++ word) first).length ≤ 
      words.length := by
        cases' hd : words.drop (idx + 1) with
        | nil => simp
        | cons first rest => 
          simp
          have : first ∈ words := by
            rw [← hd]
            exact List.mem_of_mem_drop (List.mem_cons_self first rest)
          have : first.length ≤ words.length := by
            have : first ∈ words := by
              rw [← hd]
              exact List.mem_of_mem_drop (List.mem_cons_self first rest)
            have : words.length > 0 := h_pos
            simp [words] at this
            exact Nat.le_of_lt h_pos
          exact this
    have h_lt : (match words.drop (idx + 1) with
      | [] => ""
      | first :: rest => rest.foldl (fun acc word => acc ++ " " ++ word) first).length < s.length := by
        have : words.length ≤ s.length := by
          simp [words]
          rw [List.length_splitOn_le]
        calc
          (match words.drop (idx + 1) with
          | [] => ""
          | first :: rest => rest.foldl (fun acc word => acc ++ " " ++ word) first).length
          ≤ words.length := h_bound
          _ ≤ s.length := this
    exact Nat.lt_of_le_of_lt h_bound (Nat.lt_of_le_of_ne (by
      simp [words]
      rw [List.length_splitOn_le]
    ) (by
      intro h_eq
      simp [words] at h_eq
      have : 0 < s.length := by
        exact h✝
      rw [← h_eq] at this
      simp at this
    ))
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
                induction s.splitOn " " generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    have : word = head ∧ idx = 0 := by
                      simp [h_find]
                    simp [List.mem_cons, this.1]
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      have : word = val.1 ∧ idx = val.2 + 1 := by
                        simp [h_find]
                      simp [List.mem_cons]
                      right
                      exact ih val.2 h_find_rest
              have h_count : count_consonants word = n := by
                induction s.splitOn " " generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    have : word = head ∧ idx = 0 := by
                      simp [h_find]
                    rw [this.1]
                    exact h_count
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      have : word = val.1 ∧ idx = val.2 + 1 := by
                        simp [h_find]
                      rw [this.1]
                      exact ih val.2 h_find_rest
              have h_all_spec : (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length ≠ n := by
                apply h_all
                exact h_mem
              rw [count_consonants_eq] at h_all_spec
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
          · induction s.splitOn " " generalizing idx with
            | nil => simp [find_first_word_with_consonants] at h_find
            | cons head tail ih =>
              simp [find_first_word_with_consonants] at h_find
              by_cases h_count : count_consonants head = n
              · simp [h_count] at h_find
                have : word = head ∧ idx = 0 := by
                  simp [h_find]
                rw [this.1]
                simp [List.mem_cons]
              · simp [h_count] at h_find
                cases' h_find_rest : find_first_word_with_consonants tail n with
                | none => simp [h_find_rest] at h_find
                | some val =>
                  simp [h_find_rest] at h_find
                  have : word = val.1 ∧ idx = val.2 + 1 := by
                    simp [h_find]
                  rw [this.1]
                  simp [List.mem_cons]
                  right
                  exact ih val.2 h_find_rest
          constructor
          · induction s.splitOn " " generalizing idx with
            | nil => simp [find_first_word_with_consonants] at h_find
            | cons head tail ih =>
              simp [find_first_word_with_consonants] at h_find
              by_cases h_count : count_consonants head = n
              · simp [h_count] at h_find
                have : word = head ∧ idx = 0 := by
                  simp [h_find]
                rw [this.1, count_consonants_eq]
                exact h_count
              · simp [h_count] at h_find
                cases' h_find_rest : find_first_word_with_consonants tail n with
                | none => simp [h_find_rest] at h_find
                | some val =>
                  simp [h_find_rest] at h_find
                  have : word = val.1 ∧ idx = val.2 + 1 := by
                    simp [h_find]
                  rw [this.1, count_consonants_eq]
                  exact ih val.2 h_find_rest
          constructor
          · intro i h_lt
            simp [List.indexOf_eq_length]
            have h_first_idx : (s.splitOn " ").indexOf word = idx := by
              induction s.splitOn " " generalizing idx with
              | nil => simp [find_first_word_with_consonants] at h_find
              | cons head tail ih =>
                simp [find_first_word_with_consonants] at h_find
                by_cases h_count : count_consonants head = n
                · simp [h_count] at h_find
                  have : word = head ∧ idx = 0 := by
                    simp [h_find]
                  rw [this.1]
                  simp [List.indexOf_cons_eq]
                · simp [h_count] at h_find
                  cases' h_find_rest : find_first_word_with_consonants tail n with
                  | none => simp [h_find_rest] at h_find
                  | some val =>
                    simp [h_find_rest] at h_find
                    have : word = val.1 ∧ idx = val.2 + 1 := by
                      simp [h_find]
                    rw [this.1]
                    simp [List.indexOf_cons_ne]
                    simp [List.indexOf_eq_length]
                    have : word ≠ head := by
                      intro h_eq
                      rw [h_eq] at h_count
                      exact h_count (ih val.2 h_find_rest)
                    simp [this]
                    calc
                      tail.indexOf word + 1 = val.2 + 1 := by
                        congr
                        exact ih val.2 h_find_rest
                      _ = idx := by
                        rw [this.2]
            rw [h_first_idx] at h_lt
            have h_len_bound : i < (s.splitOn " ").length := by
              rw [h_first_idx] at h_lt
              have : idx < (s.splitOn " ").length := by
                induction s.splitOn " " generalizing idx with
                | nil => simp [find_first_word_with_consonants] at h_find
                | cons head tail ih =>
                  simp [find_first_word_with_consonants] at h_find
                  by_cases h_count : count_consonants head = n
                  · simp [h_count] at h_find
                    have : word = head ∧ idx = 0 := by
                      simp [h_find]
                    rw [this.2]
                    simp
                  · simp [h_count] at h_find
                    cases' h_find_rest : find_first_word_with_consonants tail n with
                    | none => simp [h_find_rest] at h_find
                    | some val =>
                      simp [h_find_rest] at h_find
                      have : word = val.1 ∧ idx = val.2 + 1 := by
                        simp [h_find]
                      rw [this.2]
                      simp
                      exact Nat.succ_lt_succ (ih val.2 h_find_rest)
              exact Nat.lt_trans h_lt this
            have h_get : (s.splitOn " ")[i]! = (s.splitOn " ").get ⟨i, h_len_bound⟩ := by
              simp [List.getElem_eq_get]
            rw [h_get, count_consonants_eq]
            by_contra h_eq
            have : find_first_word_with_consonants (s.splitOn " ") n = some ((s.splitOn " ").get ⟨i, h_len_bound⟩, i) := by
              induction s.splitOn " " generalizing i with
              | nil => simp at h_len_bound
              | cons head tail ih =>
                simp [find_first_word_with_consonants]
                by_cases h_i : i = 0
                · rw [h_i] at h_eq
                  simp at h_eq
                  rw [count_consonants_eq] at h_eq
                  simp [h_eq]
                · simp [h_i]
                  have : i > 0 := Nat.pos_of_ne_zero h_i
                  have : i - 1 < tail.length := by
                    simp at h_len_bound
                    exact Nat.sub_lt_right_of_lt_add this h_len_bound
                  rw [← ih (i - 1)]
                  simp
                  congr
                  simp [List.get_cons_succ]
                  congr
                  exact Nat.succ_pred_eq_of_ne_zero h_i
            have h_find_i : find_first_word_with_consonants (s.splitOn " ") n = some (word, idx) := h_find
            have h_unique : (s.splitOn " ").get ⟨i, h_len_bound⟩ = word ∧ i = idx := by
              rw [h_find_i] at this
              simp at this
              exact this
            rw [h_unique.2] at h_lt
            exact Nat.lt_irrefl idx h_lt
          · by_cases h_remaining : join_words_from (s.splitOn " ") (idx + 1) = ""
            · simp [h_remaining] at h_nonempty
              simp [h_remaining]
              simp [implementation]
              simp [h_remaining]
            · simp [h_remaining] at h_nonempty
              simp [h_remaining]
              simp [implementation]
              simp [h_remaining]

-- LLM HELPER
lemma count_consonants_eq (word: String) : count_consonants word = (word.data.filter (fun c => c ∉ ['a', 'e', 'i', 'o', 'u'] ∧ c ∉ ['A', 'E', 'I', 'O', 'U'] ∧ c.isAlpha)).length := by
  unfold count_consonants
  congr 1
  ext c
  simp [is_consonant]