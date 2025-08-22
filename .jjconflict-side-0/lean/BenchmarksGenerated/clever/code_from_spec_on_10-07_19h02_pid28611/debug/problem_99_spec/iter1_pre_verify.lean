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
lemma round_satisfies_spec (s: String) (integer_part: String) (decimal_part: String) 
  (is_negative: Bool) (result: Int) :
  s.split (fun c => c = '.') = [integer_part, decimal_part] →
  result = round_to_nearest_int decimal_part integer_part.toInt! is_negative →
  is_negative = (s.data.head! = '-') →
  |((integer_part.toInt! - result) : ℚ)| ≤ 0.5 ∧
  (is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? < result) ∧
  (¬is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? > result) := by
  intro h1 h2 h3
  simp [round_to_nearest_int] at h2
  constructor
  · by_cases h : decimal_part.length = 0
    · simp [h] at h2
      rw [h2]
      simp
    · simp [h] at h2
      by_cases h4 : decimal_part.data.head!.toNat >= 53
      · simp [h4] at h2
        by_cases h5 : is_negative
        · simp [h5] at h2
          rw [h2]
          simp
          norm_num
        · simp [h5] at h2
          rw [h2]
          simp
          norm_num
      · simp [h4] at h2
        rw [h2]
        simp
  · constructor
    · intro h_neg h_eq
      by_cases h : decimal_part.length = 0
      · simp [h] at h2
        rw [h2] at h_eq
        simp at h_eq
      · simp [h] at h2
        by_cases h4 : decimal_part.data.head!.toNat >= 53
        · simp [h4] at h2
          simp [h_neg] at h2
          rw [h2] at h_eq
          simp at h_eq
          simp [h_neg, h2]
          norm_num
        · simp [h4] at h2
          rw [h2] at h_eq
          simp at h_eq
    · intro h_pos h_eq
      by_cases h : decimal_part.length = 0
      · simp [h] at h2
        rw [h2] at h_eq
        simp at h_eq
      · simp [h] at h2
        by_cases h4 : decimal_part.data.head!.toNat >= 53
        · simp [h4] at h2
          simp [h_pos] at h2
          rw [h2] at h_eq
          simp at h_eq
          simp [h_pos, h2]
          norm_num
        · simp [h4] at h2
          rw [h2] at h_eq
          simp at h_eq

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
              let integer_part := parts.get! 0
              let decimal_part := parts.get! 1
              let is_negative := s.data.head! = '-'
              have h4 : parts = [integer_part, decimal_part] := by
                simp [integer_part, decimal_part]
                have : parts.length = 2 := h2
                cases' parts with hd tl
                · simp at this
                · cases' tl with hd2 tl2
                  · simp at this
                  · cases' tl2 with hd3 tl3
                    · simp
                    · simp at this
              exact round_satisfies_spec s integer_part decimal_part is_negative 
                (round_to_nearest_int decimal_part integer_part.toInt! is_negative) h4 rfl rfl
        · simp [h1, h2]
          rw [valid_string_iff]
          exact h
    · simp [h]
      rw [valid_string_iff] at h
      exact h