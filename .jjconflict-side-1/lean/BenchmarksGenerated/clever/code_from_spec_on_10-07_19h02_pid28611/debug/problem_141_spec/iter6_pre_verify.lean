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
lemma string_count_eq_filter_length (s : String) (c : Char) :
  s.toList.count c = (s.toList.filter (· = c)).length := by
  rw [List.count_eq_length_filter]

-- LLM HELPER
lemma string_split_dot_exists (file_name : String) :
  (file_name.toList.filter (· = '.')).length = 1 →
  ∃ before after : String, file_name = before ++ "." ++ after := by
  intro h
  have h_count : file_name.toList.count '.' = 1 := by
    rw [←string_count_eq_filter_length]
    exact h
  have h_mem : '.' ∈ file_name.toList := by
    rw [←List.count_pos_iff]
    rw [h_count]
    norm_num
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_mem
  use (file_name.toList.take i).asString, (file_name.toList.drop (i + 1)).asString
  have h_eq : file_name.toList = file_name.toList.take i ++ ['.'] ++ file_name.toList.drop (i + 1) := by
    have : file_name.toList.get i = '.' := hi
    rw [←List.take_append_drop i file_name.toList]
    have h_get : file_name.toList.get i = '.' := this
    have h_drop : file_name.toList.drop i = '.' :: file_name.toList.drop (i + 1) := by
      rw [←List.get_cons_drop i file_name.toList]
      rw [h_get]
    rw [←List.take_append_drop i file_name.toList]
    rw [h_drop]
    simp
  rw [←String.toList_inj]
  simp [String.toList_append, String.toList_asString]
  exact h_eq

-- LLM HELPER
lemma string_split_correct (file_name : String) :
  (file_name.toList.filter (· = '.')).length = 1 →
  ∃ before after : String, file_name = before ++ "." ++ after ∧ 
  file_name.split (· = '.') = [before, after] := by
  intro h
  obtain ⟨before, after, h_eq⟩ := string_split_dot_exists file_name h
  use before, after
  constructor
  · exact h_eq
  · rw [h_eq]
    have : String.split (before ++ "." ++ after) (· = '.') = [before, after] := by
      rw [String.split_append_single]
      simp
    exact this

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
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, 
               not_or, not_not] at h
    obtain ⟨h_digit, h_dot, h_rest⟩ := h
    constructor
    · exact h_digit
    constructor
    · exact h_dot
    · split at h_rest
      case h_1 before after h_split =>
        obtain ⟨h_nonempty, h_first_some, h_alpha, h_ext⟩ := h_rest
        obtain ⟨before', after', h_eq, h_split_eq⟩ := string_split_correct file_name h_dot
        have h_eq_split : [before, after] = [before', after'] := by
          rw [←h_split_eq, h_split]
        have h_before_eq : before = before' := by
          injection h_eq_split
        have h_after_eq : after = after' := by
          injection h_eq_split with h1 h2
          injection h2
        use before', after'
        constructor
        · exact h_eq
        constructor
        · rw [←h_before_eq]; exact h_nonempty
        constructor
        · rw [←h_before_eq]; exact h_alpha
        · rw [←h_after_eq]; exact h_ext
      case h_2 =>
        contradiction
  · intro h
    obtain ⟨h_digit, h_dot, before, after, h_eq, h_nonempty, h_alpha, h_ext⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, 
               not_or, not_not]
    constructor
    · exact h_digit
    constructor
    · exact h_dot
    · obtain ⟨before', after', h_eq', h_split_eq⟩ := string_split_correct file_name h_dot
      have h_unique : before = before' ∧ after = after' := by
        have : before ++ "." ++ after = before' ++ "." ++ after' := by
          rw [←h_eq, h_eq']
        have h_app_inj : String.append before ("." ++ after) = String.append before' ("." ++ after') := by
          rw [←String.append_assoc, ←String.append_assoc, this]
        have h_before : before = before' := by
          cases String.append_left_cancel h_app_inj with
          | intro h_before h_rest =>
            exact h_before
        have h_after : after = after' := by
          have h_rest : "." ++ after = "." ++ after' := by
            rw [←h_before] at h_app_inj
            exact String.append_left_cancel h_app_inj
          exact String.append_left_cancel h_rest
        exact ⟨h_before, h_after⟩
      obtain ⟨h_before_eq, h_after_eq⟩ := h_unique
      rw [h_split_eq, h_before_eq, h_after_eq]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rw [←h_before_eq]; exact h_nonempty
      constructor
      · rw [←h_before_eq]
        simp [String.get?_eq_some_iff]
        exact ⟨0, by simp [h_nonempty]⟩
      constructor
      · rw [←h_before_eq]; exact h_alpha
      · rw [←h_after_eq]; exact h_ext

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