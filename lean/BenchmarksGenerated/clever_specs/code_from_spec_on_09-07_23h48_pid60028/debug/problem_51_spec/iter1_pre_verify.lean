def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
let is_consonant (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c);
-- spec
let spec (result: String) :=
result.all (λ c => is_consonant c) ∧ result.length ≤ string.length ∧
∀ c, result.contains c → string.contains c ∧
∀ c , string.contains c ∧ is_consonant c → (result.contains c);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def is_consonant (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c)

def implementation (string: String) : String := 
  string.filter is_consonant

-- LLM HELPER
lemma filter_all_satisfy (s: String) (p: Char → Bool) : (s.filter p).all p := by
  induction s with
  | nil => simp [String.filter, String.all]
  | cons c s ih =>
    simp [String.filter, String.all]
    split
    · simp [String.all]
      exact ih
    · exact ih

-- LLM HELPER
lemma filter_length_le (s: String) (p: Char → Bool) : (s.filter p).length ≤ s.length := by
  induction s with
  | nil => simp [String.filter]
  | cons c s ih =>
    simp [String.filter]
    split
    · simp
      exact Nat.succ_le_succ ih
    · exact Nat.le_succ_of_le ih

-- LLM HELPER
lemma filter_contains_subset (s: String) (p: Char → Bool) : ∀ c, (s.filter p).contains c → s.contains c := by
  induction s with
  | nil => 
    intro c h
    simp [String.filter] at h
  | cons a s ih =>
    intro c h
    simp [String.filter] at h
    split at h
    · simp [String.contains] at h
      simp [String.contains]
      cases h with
      | inl h => left; exact h
      | inr h => right; exact ih c h
    · simp [String.contains]
      right
      exact ih c h

-- LLM HELPER
lemma filter_contains_all_satisfying (s: String) (p: Char → Bool) : 
  ∀ c, s.contains c ∧ p c → (s.filter p).contains c := by
  induction s with
  | nil => 
    intro c h
    simp [String.contains] at h
  | cons a s ih =>
    intro c h
    simp [String.contains] at h
    simp [String.filter]
    split
    · simp [String.contains]
      cases h with
      | mk h_contains h_prop =>
        cases h_contains with
        | inl h_eq => 
          left
          exact h_eq
        | inr h_in => 
          right
          exact ih c ⟨h_in, h_prop⟩
    · cases h with
      | mk h_contains h_prop =>
        cases h_contains with
        | inl h_eq => 
          subst h_eq
          simp at *
        | inr h_in => 
          exact ih c ⟨h_in, h_prop⟩

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  let is_consonant := fun c => 
    let vowels := "aeiouAEIOU"
    not (vowels.contains c)
  use s.filter is_consonant
  constructor
  · rfl
  · constructor
    · exact filter_all_satisfy s is_consonant
    · constructor
      · exact filter_length_le s is_consonant
      · constructor
        · exact filter_contains_subset s is_consonant
        · exact filter_contains_all_satisfying s is_consonant