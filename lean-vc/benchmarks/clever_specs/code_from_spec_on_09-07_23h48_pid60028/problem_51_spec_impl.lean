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

-- LLM HELPER
def string_filter (s: String) (p: Char → Bool) : String :=
  s.data.filter p |>.asString

def implementation (string: String) : String := 
  string_filter string is_consonant

-- LLM HELPER
lemma filter_all_satisfy (s: String) (p: Char → Bool) : (string_filter s p).all p := by
  simp [string_filter, String.all]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp [List.filter]
    split
    · simp [List.asString, String.all]
      exact ih
    · exact ih

-- LLM HELPER
lemma filter_length_le (s: String) (p: Char → Bool) : (string_filter s p).length ≤ s.length := by
  simp [string_filter]
  have h: (s.data.filter p).length ≤ s.data.length := List.length_filter_le s.data p
  simp [String.length] at h
  exact h

-- LLM HELPER
lemma filter_contains_subset (s: String) (p: Char → Bool) : ∀ c, (string_filter s p).contains c → s.contains c := by
  intro c h
  simp [string_filter, String.contains, List.asString] at h
  simp [String.contains]
  have: c ∈ s.data.filter p := h
  have: c ∈ s.data := List.mem_of_mem_filter this
  exact this

-- LLM HELPER
lemma filter_contains_all_satisfying (s: String) (p: Char → Bool) : 
  ∀ c, s.contains c ∧ p c → (string_filter s p).contains c := by
  intro c h
  cases h with
  | mk h_contains h_prop =>
    simp [string_filter, String.contains, List.asString]
    simp [String.contains] at h_contains
    exact List.mem_filter_of_mem h_contains h_prop

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  let is_consonant := fun c => 
    let vowels := "aeiouAEIOU"
    not (vowels.contains c)
  use string_filter s is_consonant
  constructor
  · rfl
  · constructor
    · exact filter_all_satisfy s is_consonant
    · constructor
      · exact filter_length_le s is_consonant
      · constructor
        · exact filter_contains_subset s is_consonant
        · exact filter_contains_all_satisfying s is_consonant