import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Option Int)
-- inputs
(s: String) :=
-- spec
let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
let is_valid_string :=
  s.length > 0 ∧
  s.count (".".get! 0) ≤ 1 ∧
  s.count ("-".get! 0) ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  (s.count ("-".get! 0) = 1 → s.data.head! = '-')

let spec (result : Option Int) := match result with
  | some result =>
    is_valid_string ∧
    let parts := s.split (fun c => c = '.')
    (parts.length = 1 → result = s.toInt!) ∧
    (parts.length = 2 →
      let integer_part := parts.get! 0
      let is_negative := s.data.head! = '-'
      |((integer_part.toInt! - result) : ℚ)| ≤ 0.5 ∧
      (is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? < result) ∧
      (¬is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? > result)
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
  s.count (".".get! 0) ≤ 1 &&
  s.count ("-".get! 0) ≤ 1 &&
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) &&
  (s.count ("-".get! 0) = 1 → s.data.head! = '-')

-- LLM HELPER
def round_to_nearest_int (q: ℚ) : Int :=
  let floor_q := Int.floor q
  let frac := q - floor_q
  if frac < 0.5 then floor_q
  else if frac > 0.5 then floor_q + 1
  else if q ≥ 0 then floor_q + 1  -- tie-breaking: round away from zero
  else floor_q

def implementation (s: String) : Option Int :=
  if ¬is_valid_numeric_string s then none
  else
    let parts := s.split (fun c => c = '.')
    if parts.length = 1 then
      some s.toInt!
    else if parts.length = 2 then
      let integer_part := parts.get! 0
      let decimal_part := parts.get! 1
      if decimal_part.length = 0 then
        some integer_part.toInt!
      else
        let first_decimal := decimal_part.data.head!
        let is_negative := s.data.head! = '-'
        let base := integer_part.toInt!
        if first_decimal.toNat - '0'.toNat < 5 then
          some base
        else if first_decimal.toNat - '0'.toNat > 5 then
          if is_negative then some (base - 1) else some (base + 1)
        else  -- first_decimal = '5'
          if is_negative then some (base - 1) else some (base + 1)
    else none

-- LLM HELPER
lemma valid_string_iff (s: String) :
  is_valid_numeric_string s = true ↔
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  s.length > 0 ∧
  s.count (".".get! 0) ≤ 1 ∧
  s.count ("-".get! 0) ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  (s.count ("-".get! 0) = 1 → s.data.head! = '-') := by
  simp [is_valid_numeric_string]
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  simp only [implementation]
  split_ifs with h
  · -- Case: invalid string
    use none
    constructor
    · rfl
    · simp
      rw [← valid_string_iff] at h
      simp at h
      exact h
  · -- Case: valid string
    simp at h
    rw [← valid_string_iff] at h
    let parts := s.split (fun c => c = '.')
    by_cases h_parts : parts.length = 1
    · -- No decimal point
      use some s.toInt!
      constructor
      · simp [parts]
        rw [if_pos h_parts]
      · simp
        constructor
        · exact h
        · constructor
          · intro h_eq
            simp at h_eq
            rfl
          · intro h_neq
            simp at h_neq
            contradiction
    · -- Has decimal point
      by_cases h_parts2 : parts.length = 2
      · -- Exactly one decimal point
        let integer_part := parts.get! 0
        let decimal_part := parts.get! 1
        by_cases h_empty : decimal_part.length = 0
        · -- Empty decimal part
          use some integer_part.toInt!
          constructor
          · simp [parts, h_parts2, h_empty]
          · simp
            constructor
            · exact h
            · constructor
              · intro h_eq
                simp at h_eq
                contradiction
              · intro h_eq
                simp at h_eq
                rfl
        · -- Non-empty decimal part
          let first_decimal := decimal_part.data.head!
          let is_negative := s.data.head! = '-'
          let base := integer_part.toInt!
          by_cases h_lt5 : first_decimal.toNat - '0'.toNat < 5
          · -- First decimal digit < 5
            use some base
            constructor
            · simp [parts, h_parts2, h_empty, h_lt5]
            · simp
              constructor
              · exact h
              · constructor
                · intro h_eq
                  simp at h_eq
                  contradiction
                · intro h_eq
                  simp at h_eq
                  sorry -- This requires detailed reasoning about decimal rounding
          · -- First decimal digit ≥ 5
            by_cases h_gt5 : first_decimal.toNat - '0'.toNat > 5
            · -- First decimal digit > 5
              use some (if is_negative then base - 1 else base + 1)
              constructor
              · simp [parts, h_parts2, h_empty, h_lt5, h_gt5]
              · simp
                constructor
                · exact h
                · sorry -- This requires detailed reasoning about decimal rounding
            · -- First decimal digit = 5
              use some (if is_negative then base - 1 else base + 1)
              constructor
              · simp [parts, h_parts2, h_empty, h_lt5, h_gt5]
              · simp
                constructor
                · exact h
                · sorry -- This requires detailed reasoning about decimal rounding
      · -- Invalid number of parts
        use none
        constructor
        · simp [parts]
          rw [if_neg h_parts, if_neg h_parts2]
        · simp
          sorry -- This case should not occur for valid strings