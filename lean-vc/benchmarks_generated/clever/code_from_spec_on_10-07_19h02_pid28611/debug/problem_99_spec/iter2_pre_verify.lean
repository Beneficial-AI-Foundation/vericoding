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
def round_to_nearest_int (decimal_part: String) (integer_part: Int) (is_negative: Bool) : Int :=
  if decimal_part.length = 0 then integer_part
  else
    let first_digit := decimal_part.data.head!
    if first_digit.toNat >= 53 then -- '5' is 53 in ASCII
      if is_negative then integer_part - 1 else integer_part + 1
    else integer_part

def implementation (s: String) : Option Int :=
  if !is_valid_numeric_string s then none
  else
    let parts := s.split (fun c => c = '.')
    if parts.length = 1 then some s.toInt!
    else if parts.length = 2 then
      let integer_part := parts.get! 0
      let decimal_part := parts.get! 1
      let is_negative := s.data.head! = '-'
      let int_val := integer_part.toInt!
      some (round_to_nearest_int decimal_part int_val is_negative)
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

-- LLM HELPER
lemma split_length_two (s: String) (parts: List String) :
  parts = s.split (fun c => c = '.') →
  parts.length = 2 →
  ∃ integer_part decimal_part, parts = [integer_part, decimal_part] := by
  intro h1 h2
  rw [h1] at h2
  have : parts.length = 2 := h2
  cases' parts with hd tl
  · simp at this
  · cases' tl with hd2 tl2
    · simp at this
    · cases' tl2 with hd3 tl3
      · simp
        use hd, hd2
        simp
      · simp at this

-- LLM HELPER
lemma round_abs_le_half (decimal_part: String) (integer_part: Int) (is_negative: Bool) :
  |((integer_part - round_to_nearest_int decimal_part integer_part is_negative) : ℚ)| ≤ 0.5 := by
  simp [round_to_nearest_int]
  by_cases h : decimal_part.length = 0
  · simp [h]
    norm_num
  · simp [h]
    by_cases h4 : decimal_part.data.head!.toNat >= 53
    · simp [h4]
      by_cases h5 : is_negative
      · simp [h5]
        norm_num
      · simp [h5]
        norm_num
    · simp [h4]
      norm_num

-- LLM HELPER
lemma round_tie_breaking (decimal_part: String) (integer_part: Int) (is_negative: Bool) :
  decimal_part.length > 0 →
  decimal_part.data.head!.toNat = 53 →
  |((integer_part - round_to_nearest_int decimal_part integer_part is_negative) : ℚ)| = 0.5 := by
  intro h1 h2
  simp [round_to_nearest_int, h1, h2]
  norm_num

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    by_cases h : is_valid_numeric_string s
    · simp [h]
      let parts := s.split (fun c => c = '.')
      by_cases h1 : parts.length = 1
      · simp [h1]
        constructor
        · rw [valid_string_iff]
          exact h
        · intro
          rfl
      · by_cases h2 : parts.length = 2
        · simp [h1, h2]
          constructor
          · rw [valid_string_iff]
            exact h
          · constructor
            · intro h3
              contradiction
            · intro h3
              obtain ⟨integer_part, decimal_part, h4⟩ := split_length_two s parts rfl h2
              simp [h4]
              constructor
              · apply round_abs_le_half
              · constructor
                · intro h_neg h_eq
                  simp [round_to_nearest_int] at h_eq
                  by_cases h_dec : decimal_part.length = 0
                  · simp [h_dec] at h_eq
                    norm_num at h_eq
                  · simp [h_dec] at h_eq
                    by_cases h_digit : decimal_part.data.head!.toNat >= 53
                    · simp [h_digit, h_neg] at h_eq
                      norm_num at h_eq
                    · simp [h_digit] at h_eq
                      norm_num at h_eq
                · intro h_pos h_eq
                  simp [round_to_nearest_int] at h_eq
                  by_cases h_dec : decimal_part.length = 0
                  · simp [h_dec] at h_eq
                    norm_num at h_eq
                  · simp [h_dec] at h_eq
                    by_cases h_digit : decimal_part.data.head!.toNat >= 53
                    · simp [h_digit, h_pos] at h_eq
                      norm_num at h_eq
                    · simp [h_digit] at h_eq
                      norm_num at h_eq
        · simp [h1, h2]
          rw [valid_string_iff]
          exact h
    · simp [h]
      rw [← valid_string_iff] at h
      exact h