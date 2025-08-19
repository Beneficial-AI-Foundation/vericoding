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
  s.all (fun c => c = ' ' ∨ c = ',')

-- LLM HELPER
def string_remaining_length (s: String) : Nat :=
  s.length - (skip_separators s).length + 
  (skip_separators s).length - (extract_first_word (skip_separators s)).length

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
  have h5 : first.length > 0 := by
    simp [first]
    by_contra h
    simp at h
    have : first.isEmpty = true := String.length_eq_zero.mp h
    contradiction
  omega

-- LLM HELPER
theorem skip_separators_spec (s: String) : 
  (skip_separators s).all (fun c => c ≠ ' ' ∧ c ≠ ',') ∨ skip_separators s = "" := by
  by_cases h : skip_separators s = ""
  · right; exact h
  · left
    simp [skip_separators]
    exact String.all_dropWhile_not s (fun c => c = ' ' ∨ c = ',') h

-- LLM HELPER
theorem extract_first_word_spec (s: String) :
  let first := extract_first_word s
  first = s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := by
  rfl

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
                apply String.dropWhile_ne_empty_of_exists
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
              cases' String.isEmpty_iff_eq_empty.mp h1 with c hc
              exact ⟨c, hc.1, h c hc.2⟩
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
              congr 1
              · simp [extract_first_word]
                rw [String.takeWhile_eq_takeWhile]
              · simp [skip_separators]
                congr 1
                simp [extract_first_word]
                rw [String.drop_takeWhile_add_one]
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