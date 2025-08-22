def problem_spec
-- function signature
(impl: List String → String)
-- inputs
(words: List String) :=
let unique_chars (string: String) :=
  let string_idx := {i: Nat | i < string.length}.toFinset
  let characters := string_idx.image (fun i => string.toList.get! i)
  characters.card
-- spec
let spec (result: String) :=
(result = "" ↔ words.length = 0) ∧
(words.length != 0 → result ∈ words ∧
let unique_chars_list := words.map unique_chars
let max_unique_chars := unique_chars_list.max?.get!
unique_chars result = max_unique_chars ∧
∀ i : Nat, i < words.length →
  unique_chars_list[i]! = max_unique_chars →
  result ≤ words[i]!)
-- program terminates
∃ result, impl words = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def unique_chars (string: String) : Nat :=
  let string_idx := {i: Nat | i < string.length}.toFinset
  let characters := string_idx.image (fun i => string.toList.get! i)
  characters.card

-- LLM HELPER
instance : Min String where
  min := fun a b => if a ≤ b then a else b

-- LLM HELPER
def find_min_with_max_unique_chars (words: List String) : String :=
  if words.isEmpty then ""
  else
    let unique_chars_list := words.map unique_chars
    let max_unique_chars := unique_chars_list.max?.get!
    let candidates := words.filter (fun w => unique_chars w = max_unique_chars)
    candidates.min?.get!

def implementation (words: List String) : String := find_min_with_max_unique_chars words

-- LLM HELPER
lemma empty_case (words: List String) (h: words.length = 0) : 
  find_min_with_max_unique_chars words = "" := by
  simp [find_min_with_max_unique_chars]
  rw [List.isEmpty_iff_length_eq_zero]
  exact h

-- LLM HELPER
lemma nonempty_case (words: List String) (h: words.length ≠ 0) :
  let result := find_min_with_max_unique_chars words
  let unique_chars_list := words.map unique_chars
  let max_unique_chars := unique_chars_list.max?.get!
  result ∈ words ∧ 
  unique_chars result = max_unique_chars ∧
  ∀ i : Nat, i < words.length →
    unique_chars_list[i]! = max_unique_chars →
    result ≤ words[i]! := by
  simp [find_min_with_max_unique_chars]
  rw [List.isEmpty_iff_length_eq_zero] at h
  simp [h]
  let unique_chars_list := words.map unique_chars
  let max_unique_chars := unique_chars_list.max?.get!
  let candidates := words.filter (fun w => unique_chars w = max_unique_chars)
  have h_candidates_nonempty : candidates.length > 0 := by
    simp [candidates]
    have h_max_in_list : max_unique_chars ∈ unique_chars_list := by
      simp [max_unique_chars]
      apply List.max?_mem
      simp [unique_chars_list]
      exact List.length_pos_of_ne_zero h
    obtain ⟨i, hi_bound, hi_eq⟩ := List.mem_iff_get.mp h_max_in_list
    simp [unique_chars_list] at hi_eq
    have h_word_in_candidates : words[i]! ∈ candidates := by
      simp [candidates]
      constructor
      · exact List.getElem_mem_of_lt hi_bound
      · rw [← hi_eq]
        simp
    exact List.length_pos_of_mem h_word_in_candidates
  let result := candidates.min?.get!
  constructor
  · have h_result_in_candidates : result ∈ candidates := by
      simp [result]
      apply List.min?_mem
      exact Nat.zero_lt_of_ne_zero (Ne.symm (ne_of_gt h_candidates_nonempty))
    simp [candidates] at h_result_in_candidates
    exact h_result_in_candidates.1
  constructor
  · have h_result_in_candidates : result ∈ candidates := by
      simp [result]
      apply List.min?_mem
      exact Nat.zero_lt_of_ne_zero (Ne.symm (ne_of_gt h_candidates_nonempty))
    simp [candidates] at h_result_in_candidates
    exact h_result_in_candidates.2
  · intro i hi_bound hi_eq
    have h_word_in_candidates : words[i]! ∈ candidates := by
      simp [candidates]
      constructor
      · exact List.getElem_mem_of_lt hi_bound
      · rw [← List.getElem_map]
        exact hi_eq
    have h_result_min : result ≤ words[i]! := by
      simp [result]
      apply List.min?_le
      exact h_word_in_candidates
    exact h_result_min

theorem correctness
(words: List String) : problem_spec implementation words := by
  simp [problem_spec, implementation]
  let result := find_min_with_max_unique_chars words
  use result
  constructor
  · rfl
  · constructor
    · constructor
      · intro h_result_empty
        by_cases h : words.length = 0
        · exact h
        · have h_nonempty := nonempty_case words h
          rw [h_result_empty] at h_nonempty
          have h_empty_not_in_words : "" ∉ words := by
            intro h_empty_in
            have h_pos : 0 < words.length := List.length_pos_of_mem h_empty_in
            exact h (ne_of_gt h_pos)
          exact h_empty_not_in_words h_nonempty.1
      · intro h_words_empty
        exact empty_case words h_words_empty
    · intro h_words_nonempty
      exact nonempty_case words h_words_nonempty