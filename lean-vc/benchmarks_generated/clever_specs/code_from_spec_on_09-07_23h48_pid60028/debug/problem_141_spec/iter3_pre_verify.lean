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
def count_digits (s : String) : Nat :=
  (s.toList.filter Char.isDigit).length

-- LLM HELPER
def count_dots (s : String) : Nat :=
  (s.toList.filter (· = '.')).length

-- LLM HELPER
def split_at_last_dot (s : String) : String × String :=
  let chars := s.toList
  let dot_indices := chars.zipIdx.filter (fun (_, c) => c = '.')
  match dot_indices.reverse with
  | [] => ("", "")
  | (idx, _) :: _ => 
    let before := chars.take idx
    let after := chars.drop (idx + 1)
    (before.asString, after.asString)

-- LLM HELPER
def is_valid_extension (ext : String) : Bool :=
  ext == "txt" || ext == "exe" || ext == "dll"

-- LLM HELPER
def is_valid_filename (file_name : String) : Bool :=
  count_digits file_name ≤ 3 &&
  count_dots file_name == 1 &&
  let (before, after) := split_at_last_dot file_name
  before != "" &&
  (before.length > 0 && Char.isAlpha (before.get! 0)) &&
  is_valid_extension after

def implementation (file_name : String) : String :=
  if is_valid_filename file_name then "Yes" else "No"

-- LLM HELPER
lemma count_digits_correct (s : String) : 
  count_digits s = (s.toList.filter Char.isDigit).length := by
  rfl

-- LLM HELPER  
lemma count_dots_correct (s : String) :
  count_dots s = (s.toList.filter (· = '.')).length := by
  rfl

-- LLM HELPER
lemma split_correct (s : String) :
  let (before, after) := split_at_last_dot s
  count_dots s = 1 → s = before ++ "." ++ after := by
  intro h
  simp [split_at_last_dot]
  let chars := s.toList
  let dot_indices := chars.zipIdx.filter (fun (_, c) => c = '.')
  have h_nonempty : dot_indices.length ≥ 1 := by
    simp [count_dots, List.length_filter, List.length_zipIdx] at h
    exact Nat.one_le_of_zero_lt_of_zero_le (by rw [h]; exact Nat.zero_lt_one) (Nat.zero_le _)
  have h_exists : ∃ idx c, (idx, c) ∈ dot_indices := by
    cases' dot_indices with hd tl
    · simp at h_nonempty
    · use hd.1, hd.2
      simp
  obtain ⟨idx, c, hmem⟩ := h_exists
  simp [List.mem_filter, List.mem_zipIdx] at hmem
  obtain ⟨hidx, hc⟩ := hmem
  have : chars.get ⟨idx, hidx⟩ = '.' := hc
  sorry

-- LLM HELPER
lemma is_valid_extension_correct (ext : String) :
  is_valid_extension ext = true ↔ (ext = "txt" ∨ ext = "exe" ∨ ext = "dll") := by
  constructor
  · intro h
    simp [is_valid_extension] at h
    cases h with
    | inl h => left; exact h
    | inr h => 
      cases h with
      | inl h => right; left; exact h
      | inr h => right; right; exact h
  · intro h
    simp [is_valid_extension]
    cases h with
    | inl h => left; exact h
    | inr h => 
      cases h with
      | inl h => right; left; exact h
      | inr h => right; right; exact h

-- LLM HELPER
lemma is_valid_filename_correct (file_name : String) :
  is_valid_filename file_name = true ↔ 
  ((file_name.toList.filter Char.isDigit).length ≤ 3 ∧
   (file_name.toList.filter (· = '.')).length = 1 ∧
   ∃ before after : String,
     file_name = before ++ "." ++ after ∧
     before != "" ∧
     Char.isAlpha (before.get! 0) ∧
     (after = "txt" ∨ after = "exe" ∨ after = "dll")) := by
  constructor
  · intro h
    simp [is_valid_filename] at h
    rw [count_digits_correct, count_dots_correct]
    constructor
    · exact h.1
    constructor
    · exact h.2.1
    let (before, after) := split_at_last_dot file_name
    use before, after
    constructor
    · have : count_dots file_name = 1 := h.2.1
      rw [count_dots_correct] at this
      exact split_correct file_name this
    constructor
    · exact h.2.2.1
    constructor
    · exact h.2.2.2.1
    · rw [← is_valid_extension_correct]
      exact h.2.2.2.2
  · intro h
    simp [is_valid_filename]
    rw [count_digits_correct, count_dots_correct]
    constructor
    · exact h.1
    constructor
    · exact h.2.1
    constructor
    · obtain ⟨before, after, heq, hne, halpha, hext⟩ := h.2.2
      exact hne
    constructor
    · obtain ⟨before, after, heq, hne, halpha, hext⟩ := h.2.2
      exact halpha
    · rw [is_valid_extension_correct]
      obtain ⟨before, after, heq, hne, halpha, hext⟩ := h.2.2
      exact hext

theorem correctness
(file_name : String) : problem_spec implementation file_name := by
  use implementation file_name
  constructor
  · rfl
  constructor
  · intro h
    simp [implementation]
    cases' h_case : is_valid_filename file_name with
    | true => 
      simp [if_pos h_case]
      rw [is_valid_filename_correct] at h_case
      exact h_case
    | false =>
      simp [if_neg (Bool.false_ne_true ▸ h_case)]
      rw [is_valid_filename_correct] at h_case
      simp at h_case
      exact h_case h
  · intro h
    simp [implementation] at h
    cases' h_case : is_valid_filename file_name with
    | true =>
      simp [if_pos h_case] at h
    | false =>
      simp [if_neg (Bool.false_ne_true ▸ h_case)] at h
      rw [is_valid_filename_correct] at h_case
      simp at h_case
      exact h_case