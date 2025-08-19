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
def round_to_nearest_int (s: String) : Int :=
  let parts := s.split (fun c => c = '.')
  if parts.length = 1 then
    s.toInt!
  else
    let integer_part := parts.get! 0
    let decimal_part := parts.get! 1
    let is_negative := s.data.head! = '-'
    let base := integer_part.toInt!
    if decimal_part.length = 0 then
      base
    else
      let first_decimal := decimal_part.data.head!
      let decimal_value := first_decimal.toNat - '0'.toNat
      if decimal_value < 5 then
        base
      else if decimal_value > 5 then
        if is_negative then base - 1 else base + 1
      else
        -- Tie case: round to even
        if is_negative then
          if base % 2 = 0 then base else base - 1
        else
          if base % 2 = 0 then base else base + 1

def implementation (s: String) : Option Int :=
  if is_valid_numeric_string s then
    some (round_to_nearest_int s)
  else
    none

-- LLM HELPER
lemma is_valid_numeric_string_iff (s: String) :
  is_valid_numeric_string s = true ↔
  let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
  s.length > 0 ∧
  s.count (".".get! 0) ≤ 1 ∧
  s.count ("-".get! 0) ≤ 1 ∧
  s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
  (s.count ("-".get! 0) = 1 → s.data.head! = '-') := by
  unfold is_valid_numeric_string
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  tauto

-- LLM HELPER
lemma round_to_nearest_int_correct (s: String) 
  (h_valid : is_valid_numeric_string s = true) :
  let parts := s.split (fun c => c = '.')
  let result := round_to_nearest_int s
  (parts.length = 1 → result = s.toInt!) ∧
  (parts.length = 2 →
    let integer_part := parts.get! 0
    let is_negative := s.data.head! = '-'
    |((integer_part.toInt! - result) : ℚ)| ≤ 0.5 ∧
    (is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? < result) ∧
    (¬is_negative → |((integer_part.toInt! - result) : ℚ)| = 0.5 → integer_part.toInt? > result)
  ) := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  simp only [exists_eq_left]
  by_cases h : is_valid_numeric_string s
  · -- Valid case
    simp [h]
    constructor
    · rw [is_valid_numeric_string_iff] at h
      exact h
    · exact round_to_nearest_int_correct s h
  · -- Invalid case
    simp [h]
    rw [is_valid_numeric_string_iff] at h
    exact h