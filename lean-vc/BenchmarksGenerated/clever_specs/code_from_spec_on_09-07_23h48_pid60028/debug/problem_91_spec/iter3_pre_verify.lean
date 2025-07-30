def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Nat) :=
  let is_sentence_is_boredom (s: String) : Bool :=
    (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data
  match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!' ) with
  | some i =>
    let j := i + 1;
    let substring := s.drop j;
    result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    result = if is_sentence_is_boredom s then 1 else 0
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_sentence_is_boredom (s: String) : Bool :=
  (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data

-- LLM HELPER
lemma string_drop_length_decreases (s: String) (i: Nat) (h: i < s.length) : 
  (s.drop (i + 1)).length < s.length := by
  rw [String.length_drop]
  simp
  omega

def implementation (s: String) : Nat :=
  match h : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
  | some i =>
    let j := i + 1;
    let substring := s.drop j;
    (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    if is_sentence_is_boredom s then 1 else 0
termination_by s.length
decreasing_by
  have h_idx : i < s.data.length := by
    apply List.findIdx?_lt_length
    exact h
  have h_str : i < s.length := by
    rw [String.length_eq_data_length]
    exact h_idx
  apply string_drop_length_decreases
  exact h_str

theorem correctness
(s: String)
: problem_spec implementation s := by
  exists implementation s
  constructor
  · rfl
  · simp only [is_sentence_is_boredom]
    cases h : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
    | some i =>
      simp [implementation]
      rw [h]
      simp
    | none =>
      simp [implementation]
      rw [h]
      simp