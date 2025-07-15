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

-- LLM HELPER
lemma forall_char_helper (s: String) : 
  s.data.all (fun c => ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."].contains (String.mk [c])) ↔
  ∀ x ∈ s.data, String.mk [x] = "-" ∨ String.mk [x] = "0" ∨ String.mk [x] = "1" ∨ String.mk [x] = "2" ∨ 
                 String.mk [x] = "3" ∨ String.mk [x] = "4" ∨ String.mk [x] = "5" ∨ String.mk [x] = "6" ∨ 
                 String.mk [x] = "7" ∨ String.mk [x] = "8" ∨ String.mk [x] = "9" ∨ String.mk [x] = "." := by
  simp [List.all_eq_true]

-- LLM HELPER
lemma valid_string_prop_equiv (s: String) : 
  (let numeric_characters := ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."]
   s.length > 0 ∧
   s.count (".".get! 0) ≤ 1 ∧
   s.count ("-".get! 0) ≤ 1 ∧
   s.data.all (fun c => numeric_characters.contains (String.mk [c])) ∧
   (s.count ("-".get! 0) = 1 → s.data.head! = '-')) ↔
  (0 < s.length ∧
   s.count (".".get! 0) ≤ 1 ∧
   s.count ("-".get! 0) ≤ 1 ∧
   (∀ x ∈ s.data, String.mk [x] = "-" ∨ String.mk [x] = "0" ∨ String.mk [x] = "1" ∨ String.mk [x] = "2" ∨ 
                  String.mk [x] = "3" ∨ String.mk [x] = "4" ∨ String.mk [x] = "5" ∨ String.mk [x] = "6" ∨ 
                  String.mk [x] = "7" ∨ String.mk [x] = "8" ∨ String.mk [x] = "9" ∨ String.mk [x] = ".") ∧
   (s.count ("-".get! 0) = 1 → s.data.head! = '-')) := by
  simp [forall_char_helper]

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
        · rw [valid_string_iff] at h
          rw [valid_string_prop_equiv]
          exact h
        · intro
          rfl
      · by_cases h2 : parts.length = 2
        · simp [h1, h2]
          constructor
          · rw [valid_string_iff] at h
            rw [valid_string_prop_equiv]
            exact h
          · constructor
            · intro h3
              exfalso
              exact h1 h3
            · intro h3
              simp [round_to_nearest_int]
              constructor
              · by_cases h_dec : (parts.get! 1).length = 0
                · simp [h_dec]
                  norm_num
                · simp [h_dec]
                  norm_num
              · constructor
                · intro h_neg h_eq
                  simp [parts.get!]
                  norm_num at h_eq
                · intro h_pos h_eq
                  simp [parts.get!]
                  norm_num at h_eq
        · simp [h1, h2]
          rw [valid_string_iff] at h
          rw [valid_string_prop_equiv]
          exact h
    · simp [h]
      intro h_len h_dot h_dash h_chars h_dash_pos
      rw [← valid_string_iff] at h
      have h_valid : is_valid_numeric_string s = true := by
        simp [is_valid_numeric_string]
        rw [← forall_char_helper] at h_chars
        exact ⟨h_len, h_dot, h_dash, h_chars, h_dash_pos⟩
      rw [h_valid] at h
      exact h