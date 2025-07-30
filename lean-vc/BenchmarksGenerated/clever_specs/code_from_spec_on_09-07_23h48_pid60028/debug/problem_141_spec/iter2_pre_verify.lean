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
  have h_one_dot : dot_indices.length = 1 := by
    simp [count_dots, count_dots_correct] at h
    sorry
  sorry

-- LLM HELPER
lemma is_valid_extension_correct (ext : String) :
  is_valid_extension ext = true ↔ (ext = "txt" ∨ ext = "exe" ∨ ext = "dll") := by
  constructor
  · intro h
    simp [is_valid_extension] at h
    cases' h with h h
    · left; exact h
    · cases' h with h h
      · right; left; exact h
      · right; right; exact h
  · intro h
    simp [is_valid_extension]
    cases' h with h h
    · left; exact h
    · cases' h with h h
      · right; left; exact h
      · right; right; exact h

-- LLM HELPER
lemma is_valid_filename_correct (file_name : String) :
  is_valid_filename file_name = true ↔ 
  (count_digits file_name ≤ 3 ∧
   count_dots file_name = 1 ∧
   ∃ before after : String,
     file_name = before ++ "." ++ after ∧
     before != "" ∧
     Char.isAlpha (before.get! 0) ∧
     (after = "txt" ∨ after = "exe" ∨ after = "dll")) := by
  constructor
  · intro h
    simp [is_valid_filename] at h
    constructor
    · exact h.1
    constructor
    · exact h.2.1
    let (before, after) := split_at_last_dot file_name
    use before, after
    constructor
    · have : count_dots file_name = 1 := h.2.1
      exact split_correct file_name this
    constructor
    · exact h.2.2.1
    constructor
    · exact h.2.2.2.1
    · rw [← is_valid_extension_correct]
      exact h.2.2.2.2
  · intro h
    simp [is_valid_filename]
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
    split_ifs with hvalid
    · rfl
    · rw [count_digits_correct, count_dots_correct] at is_valid_filename_correct
      rw [is_valid_filename_correct] at hvalid
      simp at hvalid
      exact hvalid h
  · intro h
    simp [implementation] at h
    split_ifs at h with hvalid
    · simp at h
    · rw [count_digits_correct, count_dots_correct] at is_valid_filename_correct
      rw [is_valid_filename_correct] at hvalid
      simp at hvalid
      exact hvalid