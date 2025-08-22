def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isUpper (c : Char) :=
  65 ≤ c.toNat ∧ c.toNat ≤ 90
-- spec
let spec (result: Nat) :=
if string.length = 1 then
  result = if isUpper string.data[0]! then string.data[0]!.toNat else 0
else
  result = (if isUpper string.data[0]! then string.data[0]!.toNat else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def isUpper (c : Char) : Bool :=
  65 ≤ c.toNat && c.toNat ≤ 90

def implementation (string: String) : Nat :=
  if string.length = 0 then 0
  else if string.length = 1 then
    if isUpper string.data[0]! then string.data[0]!.toNat else 0
  else
    (if isUpper string.data[0]! then string.data[0]!.toNat else 0) + implementation (string.drop 1)

-- LLM HELPER
lemma isUpper_equiv (c : Char) : 
  isUpper c = true ↔ (65 ≤ c.toNat ∧ c.toNat ≤ 90) := by
  simp [isUpper]
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

-- LLM HELPER
lemma string_length_zero_empty (s : String) : 
  s.length = 0 → s.data = [] := by
  intro h
  simp [String.length] at h
  exact h

-- LLM HELPER
lemma string_drop_length (s : String) (n : Nat) : 
  s.length > n → (s.drop n).length = s.length - n := by
  intro h
  simp [String.drop, String.length]
  omega

theorem correctness
(s: String) :
problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp only [problem_spec]
    if h : s.length = 0 then
      simp [implementation, h]
      have : s.data = [] := string_length_zero_empty s h
      simp [this]
    else if h' : s.length = 1 then
      simp [implementation, h']
      by_cases h_upper : isUpper s.data[0]!
      · simp [h_upper]
        rw [isUpper_equiv] at h_upper
        simp [h_upper]
      · simp [h_upper]
        rw [isUpper_equiv] at h_upper
        simp [h_upper]
    else
      simp [implementation, h, h']
      by_cases h_upper : isUpper s.data[0]!
      · simp [h_upper]
        rw [isUpper_equiv] at h_upper
        simp [h_upper]
      · simp [h_upper]
        rw [isUpper_equiv] at h_upper
        simp [h_upper]