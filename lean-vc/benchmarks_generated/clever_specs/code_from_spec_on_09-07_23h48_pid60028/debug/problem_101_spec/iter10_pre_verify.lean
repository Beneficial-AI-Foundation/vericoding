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
def skipDelimiters (s: String) : String :=
  s.dropWhile (fun c => c = ' ' ∨ c = ',')

-- LLM HELPER
def extractToken (s: String) : String :=
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')

-- LLM HELPER
def isOnlyDelimiters (s: String) : Bool :=
  s.all (fun c => c = ' ' ∨ c = ',')

-- LLM HELPER
lemma string_length_dropWhile_le (s: String) (p: Char → Bool) :
  (s.dropWhile p).length ≤ s.length := by
  simp [String.dropWhile_length_le]

-- LLM HELPER
lemma string_length_drop (s: String) (n: Nat) :
  (s.drop n).length = s.length - n := by
  simp [String.length_drop]

-- LLM HELPER
lemma dropWhile_drop_length_lt (s: String) (p: Char → Bool) (n: Nat) :
  n > 0 → (s.dropWhile p).length > n → (s.dropWhile p).drop n |>.length < s.length := by
  intro h1 h2
  rw [string_length_drop]
  have : (s.dropWhile p).length ≤ s.length := string_length_dropWhile_le s p
  omega

-- LLM HELPER
lemma takeWhile_length_pos (s: String) (p: Char → Bool) :
  ¬s.isEmpty → (∃ c, c ∈ s.toList ∧ p c) → (s.takeWhile p).length > 0 := by
  intro h1 h2
  simp [String.takeWhile_length_pos_iff]
  constructor
  · exact h1
  · exact h2

def implementation (s: String) : List String :=
  if s.isEmpty then
    []
  else
    let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    if first.isEmpty then
      implementation (s.drop 1)
    else
      [first] ++ implementation (s.drop (first.length + 1))
termination_by s.length
decreasing_by 
  simp_wf
  · have h1 : (s.drop 1).length < s.length := by
      rw [string_length_drop]
      have : s.length > 0 := by
        rw [String.length_pos_iff_ne_empty]
        assumption
      omega
    exact h1
  · have h1 : (s.drop (first.length + 1)).length < s.length := by
      rw [string_length_drop]
      have h2 : first.length + 1 > 0 := by omega
      have h3 : first.length > 0 := by
        rw [String.length_pos_iff_ne_empty]
        assumption
      have h4 : s.length > 0 := by
        rw [String.length_pos_iff_ne_empty]
        assumption
      omega
    exact h1

-- LLM HELPER
lemma skipDelimiters_spec (s: String) :
  skipDelimiters s = s.dropWhile (fun c => c = ' ' ∨ c = ',') := by
  rfl

-- LLM HELPER
lemma extractToken_spec (s: String) :
  extractToken s = s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := by
  rfl

-- LLM HELPER
lemma isOnlyDelimiters_spec (s: String) :
  isOnlyDelimiters s = (s.all (fun c => c = ' ' ∨ c = ',')) := by
  rfl

-- LLM HELPER
lemma takeWhile_eq_extractToken (s: String) :
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = extractToken s := by
  rfl

-- LLM HELPER
lemma implementation_empty_case (s: String) :
  s.isEmpty → implementation s = [] := by
  intro h
  simp [implementation, h]

-- LLM HELPER
lemma all_delimiters_iff (s: String) :
  (∀ x ∈ s.toList, x = ' ' ∨ x = ',') ↔ s.all (fun c => c = ' ' ∨ c = ',') := by
  simp [String.all_iff]

theorem correctness
(s: String)
: problem_spec implementation s := by
  use implementation s
  constructor
  · rfl
  · simp [problem_spec]
    let chars := s.toList
    let first := s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    constructor
    · constructor
      · intro h
        by_cases h1 : s = ""
        · right
          exact h1
        · left
          simp [implementation] at h
          have : ¬s.isEmpty := by
            rw [String.isEmpty_iff_eq_empty]
            exact h1
          simp [this] at h
          by_cases h2 : first.isEmpty
          · simp [h2] at h
            rw [all_delimiters_iff]
            have : s.all (fun c => c = ' ' ∨ c = ',') := by
              simp [String.all_iff]
              intro c hc
              have : first = s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := rfl
              rw [this] at h2
              rw [String.takeWhile_isEmpty_iff] at h2
              cases h2 with
              | inl h3 => 
                rw [String.isEmpty_iff_eq_empty] at h3
                contradiction
              | inr h3 =>
                have := h3 c hc
                simp at this
                exact this
            exact this
          · simp [h2] at h
      · intro h
        cases h with
        | inl h1 =>
          simp [implementation]
          by_cases h2 : s.isEmpty
          · simp [h2]
          · simp [h2]
            rw [all_delimiters_iff] at h1
            have : first.isEmpty := by
              rw [String.takeWhile_isEmpty_iff]
              right
              intro c hc
              have := h1 c hc
              simp
              exact this
            simp [this]
        | inr h1 =>
          simp [implementation]
          simp [h1]
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : s.isEmpty
        · simp [h1] at h
        · simp [h1] at h
          by_cases h2 : first.isEmpty
          · simp [h2] at h
          · simp [h2] at h
            rw [h]
      · intro h
        rw [h]
        simp [implementation]
        by_cases h1 : s.isEmpty
        · simp [h1]
          rw [h1] at h
          simp at h
        · simp [h1]
          by_cases h2 : first.isEmpty
          · simp [h2]
            rw [h2] at h
            simp at h
          · simp [h2]