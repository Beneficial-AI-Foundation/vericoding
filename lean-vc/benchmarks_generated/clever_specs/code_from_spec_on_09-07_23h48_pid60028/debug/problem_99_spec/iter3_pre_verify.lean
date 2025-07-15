def problem_spec
-- function signature
(implementation: String → Option Int)
-- inputs
(s: String) :=
-- spec
let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
let is_valid_string :=
  s.length > 0 ∧
  (s.toList.filter (· = '.')).length ≤ 1 ∧
  (s.toList.filter (· = '-')).length ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  ((s.toList.filter (· = '-')).length = 1 → s.data.head! = '-')

let spec (result : Option Int) := match result with
  | some result =>
    is_valid_string ∧
    let parts := s.split (fun c => c = '.')
    (parts.length = 1 → result = s.toInt!) ∧
    (parts.length = 2 →
      let integer_part := parts[0]!
      let is_negative := s.data.head! = '-'
      (abs ((integer_part.toInt! - result) : ℚ) ≤ 0.5) ∧
      (is_negative → abs ((integer_part.toInt! - result) : ℚ) = 0.5 → integer_part.toInt! < result) ∧
      (¬is_negative → abs ((integer_part.toInt! - result) : ℚ) = 0.5 → integer_part.toInt! > result)
    )
  | none => ¬ is_valid_string
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_valid_numeric_string (s: String) : Bool :=
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  s.length > 0 &&
  (s.toList.filter (· = '.')).length ≤ 1 &&
  (s.toList.filter (· = '-')).length ≤ 1 &&
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) &&
  ((s.toList.filter (· = '-')).length = 1 → s.data.head! = '-')

-- LLM HELPER
def round_to_nearest_int (s: String) : Int :=
  let parts := s.split (fun c => c = '.')
  if parts.length = 1 then
    s.toInt!
  else
    let integer_part := parts[0]!
    let decimal_part := parts[1]!
    let is_negative := s.data.head! = '-'
    let base := integer_part.toInt!
    if decimal_part.isEmpty then
      base
    else
      let first_decimal := decimal_part.data.head!
      if first_decimal.toNat - '0'.toNat ≥ 5 then
        if is_negative then base - 1 else base + 1
      else if first_decimal.toNat - '0'.toNat < 5 then
        base
      else -- exactly 5
        if is_negative then
          if base % 2 = 0 then base - 1 else base
        else
          if base % 2 = 0 then base + 1 else base

def implementation (s: String) : Option Int :=
  if is_valid_numeric_string s then
    some (round_to_nearest_int s)
  else
    none

-- LLM HELPER
lemma valid_string_iff (s: String) : 
  is_valid_numeric_string s = true ↔ 
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  s.length > 0 ∧
  (s.toList.filter (· = '.')).length ≤ 1 ∧
  (s.toList.filter (· = '-')).length ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  ((s.toList.filter (· = '-')).length = 1 → s.data.head! = '-') := by
  simp [is_valid_numeric_string]

-- LLM HELPER
lemma round_correctness (s: String) : 
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  let is_valid := s.length > 0 ∧
    (s.toList.filter (· = '.')).length ≤ 1 ∧
    (s.toList.filter (· = '-')).length ≤ 1 ∧
    s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
    ((s.toList.filter (· = '-')).length = 1 → s.data.head! = '-')
  is_valid →
  let parts := s.split (fun c => c = '.')
  let result := round_to_nearest_int s
  (parts.length = 1 → result = s.toInt!) ∧
  (parts.length = 2 →
    let integer_part := parts[0]!
    let is_negative := s.data.head! = '-'
    abs ((integer_part.toInt! - result) : ℚ) ≤ 0.5 ∧
    (is_negative → abs ((integer_part.toInt! - result) : ℚ) = 0.5 → integer_part.toInt! < result) ∧
    (¬is_negative → abs ((integer_part.toInt! - result) : ℚ) = 0.5 → integer_part.toInt! > result)
  ) := by
  intro h_valid
  simp [round_to_nearest_int]
  constructor
  · intro h_len
    simp [h_len]
  · intro h_len
    constructor
    · simp [abs_le]
      constructor
      · simp
      · simp
    · constructor
      · intro h_neg h_eq
        simp
      · intro h_pos h_eq
        simp

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use implementation s
  constructor
  · rfl
  · cases h : implementation s with
    | some result =>
      simp [implementation] at h
      split at h
      case inl h_valid =>
        simp
        constructor
        · rw [← valid_string_iff]
          exact h_valid
        · have h_round := round_correctness s
          rw [valid_string_iff] at h_valid
          exact h_round h_valid
      case inr =>
        simp at h
    | none =>
      simp [implementation] at h
      split at h
      case inl h_valid =>
        simp at h
      case inr h_invalid =>
        simp
        rw [← valid_string_iff]
        exact h_invalid