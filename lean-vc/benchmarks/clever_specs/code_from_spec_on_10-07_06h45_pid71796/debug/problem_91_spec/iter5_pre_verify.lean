def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Nat) :=
  let is_sentence_is_boredom (s: String) : Bool :=
    (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data
  match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
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
lemma string_drop_shorter (s: String) (i: Nat) : i < s.length → (s.drop (i + 1)).length < s.length := by
  intro h
  simp [String.length, String.drop]
  have : i + 1 ≤ s.data.length := by omega
  exact List.length_drop_lt this

-- LLM HELPER
lemma findIdx_bound (s: String) (i: Nat) : 
  s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') = some i → i < s.length := by
  intro h
  simp [String.length]
  exact List.findIdx?_lt_length h

def implementation (s: String) : Nat :=
  match h : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
  | some i =>
    let j := i + 1
    let substring := s.drop j
    (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    if is_sentence_is_boredom s then 1 else 0
termination_by s.length
decreasing_by
  simp_wf
  apply string_drop_shorter
  exact findIdx_bound s i h

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation, is_sentence_is_boredom]
    cases h : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!')
    case none => rfl
    case some i => rfl