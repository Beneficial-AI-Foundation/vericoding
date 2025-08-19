import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(s: String) :=
-- spec
let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
let spec (result : Int) :=
  let chars := s.toList
  (result = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ uppercase_vowels) ∧
  (1 < chars.length →
    (result - 1 = implementation (chars.drop 2).toString ↔ chars[0]! ∈ uppercase_vowels) ∨
    (result = implementation (chars.drop 2).toString ↔ chars[0]! ∉ uppercase_vowels)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_uppercase_vowel (c : Char) : Bool :=
  c = 'A' || c = 'E' || c = 'I' || c = 'O' || c = 'U'

def implementation (s: String) : Int := 
  let chars := s.toList
  match chars with
  | [] => 0
  | [c] => if is_uppercase_vowel c then 1 else 0
  | c :: rest => 
    if is_uppercase_vowel c then 
      1 + implementation rest.toString
    else 
      implementation rest.toString

-- LLM HELPER
lemma mem_uppercase_vowels (c : Char) :
  c ∈ ['A', 'E', 'I', 'O', 'U'] ↔ (c = 'A' ∨ c = 'E' ∨ c = 'I' ∨ c = 'O' ∨ c = 'U') := by
  simp only [List.mem_cons, List.mem_nil, false_or]

-- LLM HELPER
lemma is_uppercase_vowel_correct (c : Char) :
  is_uppercase_vowel c = true ↔ c ∈ ['A', 'E', 'I', 'O', 'U'] := by
  simp [is_uppercase_vowel, mem_uppercase_vowels]
  constructor
  · intro h
    cases' h with h h
    · left; exact h
    · cases' h with h h
      · right; left; exact h
      · cases' h with h h
        · right; right; left; exact h
        · cases' h with h h
          · right; right; right; left; exact h
          · right; right; right; right; exact h
  · intro h
    cases' h with h h
    · left; exact h
    · cases' h with h h
      · right; left; exact h
      · cases' h with h h
        · right; right; left; exact h
        · cases' h with h h
          · right; right; right; left; exact h
          · right; right; right; right; exact h

-- LLM HELPER
lemma implementation_counts_vowels (s : String) :
  implementation s = (s.toList.filter (fun c => c ∈ ['A', 'E', 'I', 'O', 'U'])).length := by
  induction' s.toList with c cs ih
  · simp [implementation]
  · simp [implementation]
    cases' cs with d ds
    · simp [is_uppercase_vowel_correct]
      split_ifs with h
      · simp [h]
      · simp [h]
    · simp [is_uppercase_vowel_correct]
      rw [←ih]
      split_ifs with h
      · simp [h]
        congr
        rfl
      · simp [h]
        congr
        rfl

-- LLM HELPER
lemma implementation_zero_iff (s : String) :
  implementation s = 0 ↔ ∀ c ∈ s.toList, c ∉ ['A', 'E', 'I', 'O', 'U'] := by
  rw [implementation_counts_vowels]
  simp only [List.length_eq_zero, List.filter_eq_nil]
  constructor
  · intro h c hc
    exact h c hc
  · intro h c hc
    exact h c hc

-- LLM HELPER
lemma getElem_mem {α : Type*} (l : List α) (i : Nat) (h : i < l.length) :
  l[i] ∈ l := by
  rw [List.getElem_eq_get]
  exact List.get_mem l i

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
  let spec (result : Int) :=
    let chars := s.toList
    (result = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ uppercase_vowels) ∧
    (1 < chars.length →
      (result - 1 = implementation (chars.drop 2).toString ↔ chars[0]! ∈ uppercase_vowels) ∨
      (result = implementation (chars.drop 2).toString ↔ chars[0]! ∉ uppercase_vowels)
    )
  use implementation s
  constructor
  · rfl
  · simp [spec]
    constructor
    · rw [implementation_zero_iff]
      constructor
      · intro h i hi
        by_contra h_contra
        have : s.toList[i] ∈ s.toList := getElem_mem s.toList i hi
        exact h s.toList[i] this h_contra
      · intro h c hc
        by_contra h_contra
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_get.mp hc
        exact h i hi h_contra
    · intro h_len
      cases' s.toList with c cs
      · simp at h_len
      · cases' cs with d ds
        · simp at h_len
        · simp [implementation]
          split_ifs with h_vowel
          · left
            simp [is_uppercase_vowel_correct] at h_vowel
            simp [h_vowel]
            congr
            rfl
          · right
            simp [is_uppercase_vowel_correct] at h_vowel
            simp [h_vowel]
            congr
            rfl