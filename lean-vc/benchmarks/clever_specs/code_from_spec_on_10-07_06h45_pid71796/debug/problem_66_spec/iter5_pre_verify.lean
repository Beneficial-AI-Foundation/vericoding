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
  simp [String.drop, List.drop]
  have : s.data.length > 0 := h
  have : s.data ≠ [] := by
    intro h_empty
    rw [h_empty] at this
    simp at this
  rw [List.length_drop]
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

-- LLM HELPER
lemma string_data_getElem_safe (s : String) (h : s.length > 0) : s.data[0]! = s.data[0]'(by simp; exact h) := by
  simp [List.getElem_get]

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
  
  use implementation s
  constructor
  · rfl
  · cases' Nat.eq_zero_or_pos s.length with h h
    · -- Case: empty string
      simp [implementation, spec, h]
      have : s.data = [] := by
        cases s
        simp at h
        exact h
      simp [this, String.length]
    · -- Case: non-empty string
      cases' Nat.eq_or_lt_of_le (Nat.succ_le_iff.mpr h) with h1 h1
      · -- Case: length = 1
        simp [implementation, spec, h1]
        have equiv : isUpper_spec s.data[0]! ↔ isUpper s.data[0]! = true := by
          exact isUpper_equiv s.data[0]!
        rw [equiv]
        simp [h1]
      · -- Case: length > 1
        simp [implementation, spec]
        have h_not_one : ¬(s.length = 1) := by omega
        simp [h_not_one]
        have equiv : isUpper_spec s.data[0]! ↔ isUpper s.data[0]! = true := by
          exact isUpper_equiv s.data[0]!
        rw [equiv]
        simp [h_not_one]