import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List String → String)
-- inputs
(words: List String) :=
let unique_chars (string: String) :=
  let string_idx := {i: Nat | i < string.length}.toFinset;
  let characters := string_idx.image (fun i => string.toList.get! i);
  characters.card;
-- spec
let spec (result: String) :=
(result = "" ↔ words.length = 0) ∧
(words.length != 0 → result ∈ words ∧
let unique_chars_list := words.map unique_chars;
let max_unique_chars := unique_chars_list.max?.get!;
unique_chars result = max_unique_chars ∧
∀ i : Nat, i < words.length →
  unique_chars_list[i]! = max_unique_chars →
  result ≤ words[i]!);
-- program terminates
∃ result, impl words = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def unique_chars (string: String) : Nat :=
  let string_idx := {i: Nat | i < string.length}.toFinset;
  let characters := string_idx.image (fun i => string.toList.get! i);
  characters.card

-- LLM HELPER
def find_max_unique_chars_word (words: List String) : String :=
  if words.isEmpty then
    ""
  else
    let unique_chars_list := words.map unique_chars
    let max_unique_chars := unique_chars_list.max?.get!
    let candidates := words.filter (fun w => unique_chars w = max_unique_chars)
    candidates.min?.get!

def implementation (words: List String) : String := find_max_unique_chars_word words

-- LLM HELPER
lemma unique_chars_eq : ∀ s : String, unique_chars s = 
  let string_idx := {i: Nat | i < s.length}.toFinset;
  let characters := string_idx.image (fun i => s.toList.get! i);
  characters.card := by
  intro s
  rfl

-- LLM HELPER
lemma empty_case (words: List String) : words.isEmpty → find_max_unique_chars_word words = "" := by
  intro h
  unfold find_max_unique_chars_word
  simp [h]

-- LLM HELPER
lemma nonempty_case (words: List String) : ¬words.isEmpty → 
  find_max_unique_chars_word words ∈ words := by
  intro h
  unfold find_max_unique_chars_word
  simp [h]
  have h1 : (words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!)).min?.get! ∈ 
    words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!) := by
    apply List.get!_mem_of_min?_eq_some
    simp
    have h2 : ∃ w ∈ words, unique_chars w = (words.map unique_chars).max?.get! := by
      have h3 : (words.map unique_chars).max?.get! ∈ words.map unique_chars := by
        apply List.get!_mem_of_max?_eq_some
        simp [List.map_eq_nil_iff]
        exact List.ne_nil_of_not_isEmpty h
      obtain ⟨w, hw1, hw2⟩ := List.mem_map.mp h3
      exact ⟨w, hw1, hw2.symm⟩
    obtain ⟨w, hw1, hw2⟩ := h2
    use w
    exact ⟨List.mem_filter.mpr ⟨hw1, by simp [hw2]⟩, rfl⟩
  exact List.mem_of_mem_filter h1

-- LLM HELPER
lemma nonempty_unique_chars_eq (words: List String) : ¬words.isEmpty → 
  unique_chars (find_max_unique_chars_word words) = (words.map unique_chars).max?.get! := by
  intro h
  unfold find_max_unique_chars_word
  simp [h]
  have h1 : (words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!)).min?.get! ∈ 
    words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!) := by
    apply List.get!_mem_of_min?_eq_some
    simp
    have h2 : ∃ w ∈ words, unique_chars w = (words.map unique_chars).max?.get! := by
      have h3 : (words.map unique_chars).max?.get! ∈ words.map unique_chars := by
        apply List.get!_mem_of_max?_eq_some
        simp [List.map_eq_nil_iff]
        exact List.ne_nil_of_not_isEmpty h
      obtain ⟨w, hw1, hw2⟩ := List.mem_map.mp h3
      exact ⟨w, hw1, hw2.symm⟩
    obtain ⟨w, hw1, hw2⟩ := h2
    use w
    exact ⟨List.mem_filter.mpr ⟨hw1, by simp [hw2]⟩, rfl⟩
  have h2 := List.mem_filter.mp h1
  simp at h2
  exact h2.2

-- LLM HELPER
lemma nonempty_min_property (words: List String) : ¬words.isEmpty → 
  ∀ i : Nat, i < words.length →
  (words.map unique_chars)[i]! = (words.map unique_chars).max?.get! →
  find_max_unique_chars_word words ≤ words[i]! := by
  intro h hi hmax
  unfold find_max_unique_chars_word
  simp [h]
  have h1 : words[i]! ∈ words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!) := by
    simp [List.mem_filter]
    constructor
    · exact List.getElem_mem words i hi
    · have h2 : unique_chars words[i]! = (words.map unique_chars)[i]! := by
        rw [List.getElem_map]
      rw [h2, hmax]
  have h2 : (words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!)).min?.get! ∈ 
    words.filter (fun w => unique_chars w = (words.map unique_chars).max?.get!) := by
    apply List.get!_mem_of_min?_eq_some
    simp
    use words[i]!
    exact ⟨h1, rfl⟩
  exact List.le_min?_get!_of_mem h1

theorem correctness
(words: List String)
: problem_spec implementation words := by
  unfold problem_spec implementation
  simp [unique_chars_eq]
  use find_max_unique_chars_word words
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        rw [List.length_eq_zero] at h
        exact empty_case words (List.isEmpty_of_eq_nil h)
      · intro h
        have h1 : ¬words.isEmpty := by
          intro h2
          rw [List.isEmpty_iff_length_eq_zero] at h2
          exact h h2
        exact empty_case words h1
    · intro h
      have h1 : ¬words.isEmpty := by
        intro h2
        rw [List.isEmpty_iff_length_eq_zero] at h2
        exact h h2
      constructor
      · exact nonempty_case words h1
      · constructor
        · exact nonempty_unique_chars_eq words h1
        · intro i hi hmax
          exact nonempty_min_property words h1 i hi hmax