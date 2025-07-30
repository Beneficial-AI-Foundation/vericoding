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
    -- Use the fact that there's exactly one dot
    have : file_name.toList.count '.' = 1 := by
      simp [List.count_eq_length_filter] at h
      exact h
    -- This follows from string theory but we'll use it axiomatically
    have : ∃ i, file_name.toList.get? i = some '.' ∧ 
           ∀ j, j ≠ i → file_name.toList.get? j ≠ some '.' := by
      apply List.count_eq_one_iff_exists_unique.mp this
    obtain ⟨i, hi, huniq⟩ := this
    let before_chars := file_name.toList.take i
    let after_chars := file_name.toList.drop (i + 1)
    use before_chars.asString, after_chars.asString
    have h_eq : file_name.toList = before_chars ++ ['.'] ++ after_chars := by
      rw [List.take_append_drop]
      simp [List.take_succ_get]
      rw [←List.get?_eq_some] at hi
      simp [hi]
    rw [←String.toList_inj]
    simp [String.toList_append]
    exact h_eq
  obtain ⟨before, after, h_eq⟩ := h_split
  use before, after
  constructor
  · exact h_eq
  · have h_split_eq : file_name.split (· = '.') = [before, after] := by
      rw [h_eq]
      simp [String.split_append]
    exact h_split_eq

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
  simp only [is_valid_filename]
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
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
        · have : before.get! 0 = before.get 0 := by
            simp [String.get!, String.get?_eq_get]
            rw [Option.get_some]
            exact h_first_some
          rw [this]
          exact h_alpha
        · exact h_ext
      · contradiction
  · intro h
    obtain ⟨h_digit, h_dot, before, after, h_eq, h_nonempty, h_alpha, h_ext⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · omega
    constructor
    · exact h_dot
    · have h_split := split_dot_correct file_name h_dot
      obtain ⟨before', after', h_eq', h_split_eq⟩ := h_split
      have h_unique : before = before' ∧ after = after' := by
        have : file_name = before ++ "." ++ after := h_eq
        have : file_name = before' ++ "." ++ after' := h_eq'
        rw [this] at h_eq
        have : before ++ "." ++ after = before' ++ "." ++ after' := h_eq
        have h_inj := String.append_inj_left this
        exact h_inj
      obtain ⟨h_before_eq, h_after_eq⟩ := h_unique
      rw [h_split_eq, h_before_eq, h_after_eq]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact h_nonempty
      constructor
      · rw [←h_before_eq]
        simp [String.get?_eq_some_iff]
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
  · simp only [Bool.if_true_right, Bool.if_false_right]
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