import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(file_name : String) :=
-- spec
let spec (result: String) :=
let valid := (file_name.toList.filter Char.isDigit).length ≤ 3 ∧
  (file_name.toList.filter (· = '.')).length = 1 ∧
  ∃ before after : String,
    file_name = before ++ "." ++ after ∧
    before != "" ∧
    Char.isAlpha (before.get! 0) ∧
    (after = "txt" ∨ after = "exe" ∨ after = "dll")
(result = "Yes" ↔ valid) ∧
(result = "No" ↔ ¬valid)

-- program termination
∃ result, impl file_name = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def is_valid_filename (file_name : String) : Bool :=
  let digit_count := (file_name.toList.filter Char.isDigit).length
  let dot_count := (file_name.toList.filter (· = '.')).length
  if digit_count > 3 ∨ dot_count ≠ 1 then
    false
  else
    match file_name.split (· = '.') with
    | [before, after] =>
      before ≠ "" ∧
      (before.get? 0).isSome ∧
      Char.isAlpha (before.get! 0) ∧
      (after = "txt" ∨ after = "exe" ∨ after = "dll")
    | _ => false

def implementation (file_name : String) : String := 
  if is_valid_filename file_name then "Yes" else "No"

-- LLM HELPER
lemma split_dot_correct (file_name : String) :
  (file_name.toList.filter (· = '.')).length = 1 →
  ∃ before after : String, file_name = before ++ "." ++ after ∧ 
  file_name.split (· = '.') = [before, after] := by
  intro h
  have h_split : ∃ before after : String, file_name = before ++ "." ++ after := by
    sorry -- This requires detailed string splitting theory
  obtain ⟨before, after, h_eq⟩ := h_split
  use before, after
  constructor
  · exact h_eq
  · sorry -- This requires detailed string splitting theory

-- LLM HELPER
lemma is_valid_filename_correct (file_name : String) :
  let valid := (file_name.toList.filter Char.isDigit).length ≤ 3 ∧
    (file_name.toList.filter (· = '.')).length = 1 ∧
    ∃ before after : String,
      file_name = before ++ "." ++ after ∧
      before != "" ∧
      Char.isAlpha (before.get! 0) ∧
      (after = "txt" ∨ after = "exe" ∨ after = "dll")
  is_valid_filename file_name = true ↔ valid := by
  simp [is_valid_filename]
  constructor
  · intro h
    simp at h
    obtain ⟨h_digit, h_dot, h_rest⟩ := h
    constructor
    · omega
    constructor
    · exact h_dot
    · split at h_rest
      · obtain ⟨h_nonempty, h_first_some, h_alpha, h_ext⟩ := h_rest
        have h_split := split_dot_correct file_name h_dot
        obtain ⟨before, after, h_eq, h_split_eq⟩ := h_split
        use before, after
        constructor
        · exact h_eq
        constructor
        · exact h_nonempty
        constructor
        · rw [←h_split_eq] at h_alpha
          simp at h_alpha
          exact h_alpha
        · rw [←h_split_eq] at h_ext
          simp at h_ext
          exact h_ext
      · contradiction
  · intro h
    obtain ⟨h_digit, h_dot, before, after, h_eq, h_nonempty, h_alpha, h_ext⟩ := h
    simp
    constructor
    · omega
    constructor
    · exact h_dot
    · have h_split := split_dot_correct file_name h_dot
      obtain ⟨before', after', h_eq', h_split_eq⟩ := h_split
      have h_unique : before = before' ∧ after = after' := by
        sorry -- String splitting uniqueness
      obtain ⟨h_before_eq, h_after_eq⟩ := h_unique
      rw [h_split_eq, h_before_eq, h_after_eq]
      simp
      constructor
      · exact h_nonempty
      constructor
      · rw [←h_before_eq]
        simp
        exact ⟨h_alpha⟩
      · rw [←h_after_eq]
        exact h_ext

theorem correctness
(file_name : String)
: problem_spec implementation file_name := by
  simp [problem_spec, implementation]
  use if is_valid_filename file_name then "Yes" else "No"
  constructor
  · rfl
  · simp
    let valid := (file_name.toList.filter Char.isDigit).length ≤ 3 ∧
      (file_name.toList.filter (· = '.')).length = 1 ∧
      ∃ before after : String,
        file_name = before ++ "." ++ after ∧
        before != "" ∧
        Char.isAlpha (before.get! 0) ∧
        (after = "txt" ∨ after = "exe" ∨ after = "dll")
    constructor
    · by_cases h : is_valid_filename file_name
      · simp [h]
        rw [is_valid_filename_correct] at h
        exact h
      · simp [h]
        rw [is_valid_filename_correct] at h
        exact h
    · by_cases h : is_valid_filename file_name
      · simp [h]
        rw [is_valid_filename_correct] at h
        exact h
      · simp [h]
        rw [is_valid_filename_correct] at h
        exact h