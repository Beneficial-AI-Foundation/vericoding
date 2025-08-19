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
lemma string_drop_length (s : String) : s.length > 0 → (s.drop 1).length < s.length := by
  intro h
  simp [String.drop]
  have : s.data.length > 0 := h
  have : s.data ≠ [] := by
    intro h_empty
    rw [h_empty] at this
    simp at this
  rw [List.drop_length]
  simp
  omega

-- LLM HELPER
lemma isUpper_equiv (c : Char) : (65 ≤ c.toNat ∧ c.toNat ≤ 90) ↔ isUpper c = true := by
  constructor
  · intro h
    simp [isUpper]
    exact ⟨h.1, h.2⟩
  · intro h
    simp [isUpper] at h
    exact h

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  let isUpper_spec (c : Char) := 65 ≤ c.toNat ∧ c.toNat ≤ 90
  let spec (result: Nat) :=
    if s.length = 1 then
      result = if isUpper_spec s.data[0]! then s.data[0]!.toNat else 0
    else
      result = (if isUpper_spec s.data[0]! then s.data[0]!.toNat else 0) + implementation (s.drop 1)
  
  induction' s using String.length.strong_induction_on with s ih
  cases' Nat.eq_zero_or_pos s.length with h h
  · -- Case: empty string
    simp [implementation, spec, h]
    use 0
    simp [String.length] at h
    have : s.data = [] := by
      cases s
      simp at h
      exact h
    simp [this, String.length]
  · -- Case: non-empty string
    cases' Nat.eq_or_lt_of_le (Nat.succ_le_iff.mpr h) with h1 h1
    · -- Case: length = 1
      simp [implementation, spec, h1]
      use if isUpper s.data[0]! then s.data[0]!.toNat else 0
      constructor
      · simp [h1]
        rw [isUpper_equiv]
      · simp [h1]
    · -- Case: length > 1
      simp [implementation, spec]
      have h_not_one : ¬(s.length = 1) := by omega
      simp [h_not_one]
      have h_pos : s.length > 0 := by omega
      have h_drop : (s.drop 1).length < s.length := string_drop_length s h_pos
      have ih_drop := ih (s.drop 1) h_drop
      simp [problem_spec] at ih_drop
      obtain ⟨result_drop, h_eq_drop, h_spec_drop⟩ := ih_drop
      use (if isUpper s.data[0]! then s.data[0]!.toNat else 0) + result_drop
      constructor
      · simp [h_not_one]
        rw [h_eq_drop]
        rw [isUpper_equiv]
      · simp [h_not_one]
        rw [h_eq_drop]
        rw [isUpper_equiv]