def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(s: String) :=
-- spec
let spec (result: List String) :=
  let chars := s.toList;
  let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ');
  (result = [] ↔ (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = "") ∧
  (result ≠ [] ↔ result = [first] ++ (implementation (s.drop (first.length + 1))))

-- program termination
∃ result, implementation s = result ∧
spec result

-- LLM HELPER
def skip_separators (s: String) : String :=
  s.dropWhile (fun c => c = ' ' ∨ c = ',')

-- LLM HELPER
def extract_first_word (s: String) : String :=
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')

-- LLM HELPER
def is_all_separators (s: String) : Bool :=
  s.all (fun c => decide (c = ' ' ∨ c = ','))

-- LLM HELPER
lemma String.length_dropWhile_le (s : String) (p : Char → Bool) : 
  (s.dropWhile p).length ≤ s.length := by
  simp [String.length, String.dropWhile]
  exact List.length_dropWhile_le _ _

-- LLM HELPER
lemma String.length_takeWhile_le (s : String) (p : Char → Bool) : 
  (s.takeWhile p).length ≤ s.length := by
  simp [String.length, String.takeWhile]
  exact List.length_takeWhile_le _ _

-- LLM HELPER
lemma String.length_drop (s : String) (n : Nat) : 
  (s.drop n).length = s.length - n := by
  simp [String.length, String.drop]
  exact List.length_drop _ _

-- LLM HELPER
lemma String.length_pos_iff_ne_empty (s : String) : 
  s.length > 0 ↔ s ≠ "" := by
  simp [String.length]
  exact List.length_pos_iff_ne_nil

-- LLM HELPER
lemma String.ne_empty_of_not_isEmpty (s : String) : 
  ¬s.isEmpty → s ≠ "" := by
  intro h
  simp [String.isEmpty] at h
  exact h

-- LLM HELPER
lemma extract_first_word_ne_empty_of_ne_empty (s : String) : 
  ¬s.isEmpty → ¬(s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')).isEmpty := by
  intro h
  simp [String.isEmpty, String.takeWhile]
  by_contra h_contra
  simp at h_contra
  have : s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = "" := by
    simp [String.takeWhile, String.eq_empty_iff_isEmpty] at h_contra
    exact h_contra
  simp [String.takeWhile, List.takeWhile] at this
  simp [String.isEmpty, String.eq_empty_iff_isEmpty] at h
  cases' String.toList_ne_nil_of_ne_empty h with c hc
  have : ¬(c ≠ ',' ∧ c ≠ ' ') := by
    by_contra h_pos
    simp [List.takeWhile] at this
    cases hc with
    | cons =>
      simp [List.takeWhile] at this
      cases' h_pos with h1 h2
      simp [h1, h2] at this
  simp at this
  cases this with
  | inl h1 => exact h1
  | inr h2 => exact h2

-- LLM HELPER
lemma String.all_dropWhile_not (s : String) (p : Char → Bool) : 
  s.dropWhile p ≠ "" → (s.dropWhile p).all (fun c => ¬p c) := by
  intro h
  simp [String.all, String.dropWhile]
  exact List.all_dropWhile_not _ _ (List.ne_nil_of_ne_empty h)

def implementation (s: String) : List String := 
  let trimmed := skip_separators s
  if trimmed.isEmpty then 
    []
  else
    let first := extract_first_word trimmed
    if first.isEmpty then
      []
    else
      let rest := skip_separators (trimmed.drop first.length)
      [first] ++ implementation rest
termination_by s.length
decreasing_by
  simp_wf
  have h1 : trimmed.length ≤ s.length := by
    simp [trimmed]
    exact String.length_dropWhile_le s (fun c => c = ' ' ∨ c = ',')
  have h2 : first.length ≤ trimmed.length := by
    simp [first]
    exact String.length_takeWhile_le trimmed (fun c => c ≠ ',' ∧ c ≠ ' ')
  have h3 : rest.length ≤ (trimmed.drop first.length).length := by
    simp [rest]
    exact String.length_dropWhile_le (trimmed.drop first.length) (fun c => c = ' ' ∨ c = ',')
  have h4 : (trimmed.drop first.length).length = trimmed.length - first.length := by
    exact String.length_drop trimmed first.length
  have h5 : ¬first.isEmpty := by
    simp [first]
    apply extract_first_word_ne_empty_of_ne_empty
    exact ‹¬trimmed.isEmpty›
  have h6 : first.length > 0 := by
    simp [String.length_pos_iff_ne_empty]
    exact String.ne_empty_of_not_isEmpty h5
  have h7 : rest.length < trimmed.length := by
    rw [h4] at h3
    have : first.length > 0 := h6
    linarith [h2, h3]
  linarith [h1, h7]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        by_cases h1 : s = ""
        · right; exact h1
        · left
          simp [implementation] at h
          by_cases h2 : (skip_separators s).isEmpty
          · simp [h2] at h
            intro x hx
            simp [skip_separators] at h2
            have : ∀ c ∈ s.toList, c = ' ' ∨ c = ',' := by
              intro c hc
              by_contra hnot
              simp at hnot
              have : s.dropWhile (fun c => c = ' ' ∨ c = ',') ≠ "" := by
                simp [String.dropWhile, List.dropWhile_ne_nil_of_exists]
                exact ⟨c, hc, hnot⟩
              rw [String.isEmpty_iff_eq_empty] at h2
              contradiction
            exact this x hx
          · simp [h2] at h
            by_cases h3 : (extract_first_word (skip_separators s)).isEmpty
            · simp [h3] at h
            · simp [h3] at h
      · intro h
        cases h with
        | inl h => 
          simp [implementation]
          by_cases h1 : (skip_separators s).isEmpty
          · simp [h1]
          · simp [h1]
            have : (extract_first_word (skip_separators s)).isEmpty = true := by
              simp [extract_first_word, String.isEmpty_iff_eq_empty]
              rw [String.takeWhile_eq_empty_iff]
              have h_ne_empty : skip_separators s ≠ "" := String.ne_empty_of_not_isEmpty h1
              cases' String.toList_ne_nil_of_ne_empty h_ne_empty with c hc
              exact ⟨c, hc, h c (String.mem_toList.mp hc)⟩
            simp [this]
        | inr h =>
          simp [h, implementation]
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : (skip_separators s).isEmpty
        · simp [h1] at h
        · simp [h1] at h
          by_cases h2 : (extract_first_word (skip_separators s)).isEmpty
          · simp [h2] at h
          · simp [h2] at h
            cases h with
            | cons head tail =>
              simp
              constructor
              · simp [extract_first_word]
                rfl
              · simp [skip_separators]
                rfl
      · intro h
        simp [implementation]
        by_cases h1 : (skip_separators s).isEmpty
        · simp [h1] at h
        · simp [h1]
          by_cases h2 : (extract_first_word (skip_separators s)).isEmpty
          · simp [h2] at h
          · simp [h2]
            rw [h]
            simp [extract_first_word, skip_separators]