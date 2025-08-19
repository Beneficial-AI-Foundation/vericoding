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

-- LLM HELPER
theorem skip_separators_spec (s: String) : 
  (skip_separators s).all (fun c => c ≠ ' ' ∧ c ≠ ',') ∨ skip_separators s = "" := by
  sorry

-- LLM HELPER
theorem extract_first_word_spec (s: String) :
  let first := extract_first_word s
  first = s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') := by
  rfl

-- LLM HELPER  
theorem implementation_terminates (s: String) : 
  ∃ n, (Nat.iterate (fun s => skip_separators (s.drop (extract_first_word (skip_separators s)).length)) n s).isEmpty := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · unfold implementation
    constructor
    · constructor
      · intro h
        by_cases h1 : (skip_separators s).isEmpty
        · right
          simp [skip_separators] at h1
          exact h1
        · simp [h1] at h
          left
          sorry
      · intro h
        cases h with
        | inl h => 
          by_cases h1 : (skip_separators s).isEmpty
          · simp [h1]
          · simp [h1]
            sorry
        | inr h =>
          simp [h]
    · constructor
      · intro h
        by_cases h1 : (skip_separators s).isEmpty
        · simp [h1] at h
        · simp [h1]
          by_cases h2 : (extract_first_word (skip_separators s)).isEmpty
          · simp [h2] at h
          · simp [h2]
            sorry
      · intro h
        by_cases h1 : (skip_separators s).isEmpty
        · simp [h1] at h
        · simp [h1]
          by_cases h2 : (extract_first_word (skip_separators s)).isEmpty
          · simp [h2] at h
          · simp [h2] at h ⊢
            exact h