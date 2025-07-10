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
      (Int.natAbs (integer_part.toInt! - result) ≤ 1) ∧
      (is_negative → Int.natAbs (integer_part.toInt! - result) = 1 → integer_part.toInt! < result) ∧
      (¬is_negative → Int.natAbs (integer_part.toInt! - result) = 1 → integer_part.toInt! > result)
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
      else
        base

def implementation (s: String) : Option Int :=
  if is_valid_numeric_string s then
    some (round_to_nearest_int s)
  else
    none

-- LLM HELPER
lemma all_to_filter_conversion (s: String) : 
  s.data.all (fun c => ["-", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "."].contains (String.mk [c])) ↔ 
  (∀ (x : Char), x ∈ s.data → 
    String.mk [x] = "-" ∨ String.mk [x] = "0" ∨ String.mk [x] = "1" ∨ String.mk [x] = "2" ∨ 
    String.mk [x] = "3" ∨ String.mk [x] = "4" ∨ String.mk [x] = "5" ∨ String.mk [x] = "6" ∨ 
    String.mk [x] = "7" ∨ String.mk [x] = "8" ∨ String.mk [x] = "9" ∨ String.mk [x] = ".") := by
  simp only [List.all_eq_true, List.mem_cons, List.mem_singleton]
  constructor
  · intro h x hx
    have := h x hx
    simp [List.contains] at this
    exact this
  · intro h x hx
    simp [List.contains]
    exact h x hx

-- LLM HELPER
lemma filter_to_count_conversion (s: String) : 
  (s.toList.filter (· = '.')).length = (List.filter (fun x => decide (x = '.')) s.data).length := by
  simp [String.toList]

-- LLM HELPER
lemma filter_to_count_conversion_dash (s: String) : 
  (s.toList.filter (· = '-')).length = (List.filter (fun x => decide (x = '-')) s.data).length := by
  simp [String.toList]

-- LLM HELPER
lemma split_get_zero (s: String) : 
  let parts := s.split (fun c => c = '.')
  parts.length ≥ 1 → parts[0]?.getD "" = parts[0]! := by
  intro h
  simp [List.getD, List.get?]
  split
  · simp [List.get!]
  · simp at h
    omega

-- LLM HELPER
lemma rounding_property (s: String) (h_valid: is_valid_numeric_string s = true) :
  let parts := s.split (fun c => c = '.')
  parts.length = 2 →
  let integer_part := parts[0]!
  let result := round_to_nearest_int s
  let is_negative := s.data.head! = '-'
  (Int.natAbs (integer_part.toInt! - result) ≤ 1) ∧
  (is_negative → Int.natAbs (integer_part.toInt! - result) = 1 → integer_part.toInt! < result) ∧
  (¬is_negative → Int.natAbs (integer_part.toInt! - result) = 1 → integer_part.toInt! > result) := by
  intro h_len
  simp [round_to_nearest_int, h_len]
  split
  · contradiction
  · simp only [Int.natAbs]
    constructor
    · split
      · split
        · simp [Int.natAbs]
          split
          · simp [Int.natAbs]
            omega
          · simp [Int.natAbs]
            omega
        · simp [Int.natAbs]
          omega
      · split
        · simp [Int.natAbs]
          split
          · simp [Int.natAbs]
            omega
          · simp [Int.natAbs]
            omega
        · simp [Int.natAbs]
          omega
    · constructor
      · intro h_neg h_eq
        split at h_eq
        · split at h_eq
          · simp [Int.natAbs] at h_eq
            split at h_eq
            · simp [Int.natAbs] at h_eq
              omega
            · simp [Int.natAbs] at h_eq
              omega
          · simp [Int.natAbs] at h_eq
            omega
        · split at h_eq
          · simp [Int.natAbs] at h_eq
            split at h_eq
            · simp [Int.natAbs] at h_eq
              omega
            · simp [Int.natAbs] at h_eq
              omega
          · simp [Int.natAbs] at h_eq
            omega
      · intro h_pos h_eq
        split at h_eq
        · split at h_eq
          · simp [Int.natAbs] at h_eq
            split at h_eq
            · simp [Int.natAbs] at h_eq
              omega
            · simp [Int.natAbs] at h_eq
              omega
          · simp [Int.natAbs] at h_eq
            omega
        · split at h_eq
          · simp [Int.natAbs] at h_eq
            split at h_eq
            · simp [Int.natAbs] at h_eq
              omega
            · simp [Int.natAbs] at h_eq
              omega
          · simp [Int.natAbs] at h_eq
            omega

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    split
    case inl h_valid =>
      simp [is_valid_numeric_string] at h_valid
      simp
      constructor
      · constructor
        · exact h_valid.1
        · constructor
          · rw [← filter_to_count_conversion]
            exact h_valid.2.1
          · constructor
            · rw [← filter_to_count_conversion_dash]
              exact h_valid.2.2.1
            · constructor
              · rw [← all_to_filter_conversion]
                exact h_valid.2.2.2.1
              · rw [← filter_to_count_conversion_dash]
                exact h_valid.2.2.2.2
      · constructor
        · intro h_len
          simp [round_to_nearest_int, h_len]
        · intro h_len
          have h_valid_bool : is_valid_numeric_string s = true := by
            simp [is_valid_numeric_string]
            exact h_valid
          exact rounding_property s h_valid_bool h_len
    case inr h_invalid =>
      simp [is_valid_numeric_string] at h_invalid
      intro h_len h_dot h_dash h_all h_neg_pos
      apply h_invalid
      constructor
      · exact h_len
      · constructor
        · rw [filter_to_count_conversion]
          exact h_dot
        · constructor
          · rw [filter_to_count_conversion_dash]
            exact h_dash
          · constructor
            · rw [all_to_filter_conversion]
              exact h_all
            · rw [filter_to_count_conversion_dash]
              exact h_neg_pos