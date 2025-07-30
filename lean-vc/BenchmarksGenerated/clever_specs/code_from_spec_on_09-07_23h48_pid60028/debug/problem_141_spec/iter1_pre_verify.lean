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
  let dot_indices := chars.enum.filter (fun (_, c) => c = '.')
  match dot_indices.reverse with
  | [] => ("", "")
  | (idx, _) :: _ => 
    let before := chars.take idx
    let after := chars.drop (idx + 1)
    (before.asString, after.asString)

-- LLM HELPER
def is_valid_extension (ext : String) : Bool :=
  ext = "txt" ∨ ext = "exe" ∨ ext = "dll"

-- LLM HELPER
def is_valid_filename (file_name : String) : Bool :=
  count_digits file_name ≤ 3 ∧
  count_dots file_name = 1 ∧
  let (before, after) := split_at_last_dot file_name
  before != "" ∧
  (before.length > 0 → Char.isAlpha (before.get! 0)) ∧
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
  sorry

-- LLM HELPER
lemma is_valid_extension_correct (ext : String) :
  is_valid_extension ext ↔ (ext = "txt" ∨ ext = "exe" ∨ ext = "dll") := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

-- LLM HELPER
lemma is_valid_filename_correct (file_name : String) :
  is_valid_filename file_name ↔ 
  (count_digits file_name ≤ 3 ∧
   count_dots file_name = 1 ∧
   ∃ before after : String,
     file_name = before ++ "." ++ after ∧
     before != "" ∧
     Char.isAlpha (before.get! 0) ∧
     (after = "txt" ∨ after = "exe" ∨ after = "dll")) := by
  constructor
  · intro h
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
    · by_cases hlen : before.length > 0
      · exact h.2.2.2.1 hlen
      · simp at hlen
        have : before = "" := by
          cases' before with
          | mk data =>
            simp [String.length] at hlen
            simp [List.length_eq_zero] at hlen
            simp [hlen]
        rw [this] at h
        contradiction
    · rw [is_valid_extension_correct]
      exact h.2.2.2.2
  · intro h
    constructor
    · exact h.1
    constructor
    · exact h.2.1
    constructor
    · obtain ⟨before, after, heq, hne, halpha, hext⟩ := h.2.2
      exact hne
    constructor
    · intro hlen
      obtain ⟨before, after, heq, hne, halpha, hext⟩ := h.2.2
      rw [heq] at *
      sorry
    · rw [is_valid_extension_correct]
      obtain ⟨before, after, heq, hne, halpha, hext⟩ := h.2.2
      exact hext

theorem correctness
(file_name : String)
: problem_spec implementation file_name := by
  use implementation file_name
  constructor
  · rfl
  constructor
  · intro h
    rw [count_digits_correct, count_dots_correct] at is_valid_filename_correct
    rw [is_valid_filename_correct] at h
    simp [implementation]
    split_ifs with hvalid
    · exact h
    · contradiction
  · intro h
    rw [count_digits_correct, count_dots_correct] at is_valid_filename_correct
    simp [implementation] at h
    split_ifs at h with hvalid
    · contradiction
    · rw [is_valid_filename_correct]
      exact hvalid