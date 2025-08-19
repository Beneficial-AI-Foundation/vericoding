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
lemma is_uppercase_vowel_correct (c : Char) :
  is_uppercase_vowel c = true ↔ c ∈ ['A', 'E', 'I', 'O', 'U'] := by
  simp [is_uppercase_vowel]
  constructor
  · intro h
    simp at h
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
    simp at h
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
lemma implementation_empty : implementation "" = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_single (c : Char) : 
  implementation (String.mk [c]) = if is_uppercase_vowel c then 1 else 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (c : Char) (s : String) (h : s.length > 0) :
  implementation (String.mk (c :: s.toList)) = 
  if is_uppercase_vowel c then 1 + implementation s else implementation s := by
  simp [implementation]
  cases' s.toList with hd tl
  · simp at h
  · simp

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
  · induction' s.toList using List.strongInductionOn with l ih
    simp [spec]
    constructor
    · constructor
      · intro h
        intro i hi
        by_contra h_contra
        have : implementation (String.mk l) > 0 := by
          sorry
        rw [h] at this
        simp at this
      · intro h
        sorry
    · intro h_len
      sorry