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
  s.all (fun c => decide (c = ' ' ∨ c = ','))

-- LLM HELPER
lemma string_length_dropWhile_le (s: String) (p: Char → Bool) :
  (s.dropWhile p).length ≤ s.length := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    simp [String.dropWhile]
    by_cases h : p c
    · simp [h]
      exact Nat.le_succ_of_le ih
    · simp [h]

-- LLM HELPER
lemma string_length_drop (s: String) (n: Nat) :
  (s.drop n).length = s.length - n := by
  simp [String.length_drop]

def implementation (s: String) : List String :=
  let cleaned := skipDelimiters s
  if cleaned.isEmpty ∨ isOnlyDelimiters s then
    []
  else
    let token := extractToken cleaned
    if token.isEmpty then
      implementation (cleaned.drop 1)
    else
      [token] ++ implementation (cleaned.drop token.length)
termination_by s.length
decreasing_by 
  simp_wf
  · have h1 : cleaned.drop 1 = (skipDelimiters s).drop 1 := by rfl
    rw [h1]
    have : (skipDelimiters s).drop 1 = s.dropWhile (fun c => c = ' ' ∨ c = ',').drop 1 := by rfl
    rw [this]
    have h2 : (s.dropWhile (fun c => c = ' ' ∨ c = ',')).length ≤ s.length := by
      apply string_length_dropWhile_le
    have h4 : (s.dropWhile (fun c => c = ' ' ∨ c = ',')).drop 1 |>.length = (s.dropWhile (fun c => c = ' ' ∨ c = ',')).length - 1 := string_length_drop _ 1
    rw [h4]
    omega
  · have h2 : cleaned.drop token.length = (skipDelimiters s).drop token.length := by rfl
    rw [h2]
    have : (skipDelimiters s).drop token.length = s.dropWhile (fun c => c = ' ' ∨ c = ',').drop token.length := by rfl
    rw [this]
    have h3 : (s.dropWhile (fun c => c = ' ' ∨ c = ',')).length ≤ s.length := by
      apply string_length_dropWhile_le
    have h4 : (s.dropWhile (fun c => c = ' ' ∨ c = ',')).drop token.length |>.length = (s.dropWhile (fun c => c = ' ' ∨ c = ',')).length - token.length := string_length_drop _ token.length
    rw [h4]
    omega

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
  isOnlyDelimiters s = s.all (fun c => decide (c = ' ' ∨ c = ',')) := by
  rfl

-- LLM HELPER
lemma takeWhile_eq_extractToken (s: String) :
  s.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ') = extractToken s := by
  rfl

-- LLM HELPER
lemma implementation_empty_case (s: String) :
  (skipDelimiters s).isEmpty ∨ isOnlyDelimiters s →
  implementation s = [] := by
  intro h
  simp [implementation]
  cases h with
  | inl h1 => simp [h1]
  | inr h2 => simp [h2]

-- LLM HELPER
lemma all_delimiters_iff (s: String) :
  (∀ x ∈ s.toList, x = ' ' ∨ x = ',') ↔ s.all (fun c => decide (c = ' ' ∨ c = ',')) := by
  simp [String.all_iff]
  constructor
  · intro h c hc
    have := h c hc
    simp [decide_eq_true_eq]
    exact this
  · intro h c hc
    have := h c hc
    simp [decide_eq_true_eq] at this
    exact this

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
        by_cases h1 : (∀ x ∈ chars, x = ' ' ∨ x = ',') ∨ s = ""
        · exact h1
        · simp at h1
          cases h1 with
          | inl h2 =>
            simp at h2
            push_neg at h2
            obtain ⟨x, hx_mem, hx_not⟩ := h2
            simp [implementation] at h
            have : ¬(skipDelimiters s).isEmpty ∧ ¬isOnlyDelimiters s := by
              constructor
              · simp [skipDelimiters, String.dropWhile_isEmpty_iff]
                exact h2
              · rw [isOnlyDelimiters_spec, all_delimiters_iff]
                exact h2
            simp [this] at h
          | inr h2 =>
            simp [implementation] at h
            have : s ≠ "" := h2
            have : ¬(skipDelimiters s).isEmpty ∨ ¬isOnlyDelimiters s := by
              right
              rw [isOnlyDelimiters_spec, all_delimiters_iff]
              simp [chars]
              by_cases h3 : s.toList = []
              · simp [String.toList_eq_nil_iff] at h3
                contradiction
              · simp [h3]
                obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil h3
                use c
                constructor
                · rw [hcs]
                  simp
                · simp
            simp [this] at h
      · intro h
        cases h with
        | inl h1 =>
          rw [all_delimiters_iff] at h1
          exact implementation_empty_case s (Or.inr h1)
        | inr h1 =>
          simp [implementation]
          simp [h1]
    · constructor
      · intro h
        simp [implementation] at h
        by_cases h1 : (skipDelimiters s).isEmpty ∨ isOnlyDelimiters s
        · simp [h1] at h
        · simp [h1] at h
          rw [takeWhile_eq_extractToken]
          rfl
      · intro h
        rw [takeWhile_eq_extractToken] at h
        simp [implementation]
        by_cases h1 : (skipDelimiters s).isEmpty ∨ isOnlyDelimiters s
        · have : implementation s = [] := implementation_empty_case s h1
          rw [this] at h
          simp at h
        · simp [h1]
          rfl