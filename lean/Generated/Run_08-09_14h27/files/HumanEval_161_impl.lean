/- 
function_signature: "def solve(string : String) -> String"
docstring: |
    You are given a string s.
    if s[i] is a letter, reverse its case from lower to upper or vise versa,
    otherwise keep it as it is.
    If the string contains no letters, reverse the string.
    The function should return the resulted string.
test_cases:
  - input: "1234"
    expected_output: "4321"
  - input: "ab"
    expected_output: "AB"
  - input: "#a@C"
    expected_output: "#A@c"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def swapCase (c : Char) : Char :=
  if c.isLower then c.toUpper
  else if c.isUpper then c.toLower
  else c

def implementation (s: String) : String :=
  if s.all (fun c => ¬c.isAlpha) then
    s.toList.reverse.asString
  else
    s.map swapCase

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(string : String) :=
-- spec
let spec (result: String) :=
result.length = string.length ∧
let hasNoAlphabet := string.all (λ c => not (c.isAlpha));
(hasNoAlphabet →
  result.toList = string.toList.reverse) ∧
(hasNoAlphabet = false →
  ∀ i, i < string.length →
  let c := string.get! ⟨i⟩;
  (c.isAlpha → ((c.isLower → c.toUpper = result.get! ⟨i⟩) ∨
              (c.isUpper → c.toLower = result.get! ⟨i⟩))) ∧
  (¬ c.isAlpha → c = result.get! ⟨i⟩))
-- program terminates
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma isAlpha_of_isLower (c : Char) (h : c.isLower = true) : c.isAlpha = true := by
  simp [Char.isAlpha]
  exact Or.inl h

-- LLM HELPER
lemma isAlpha_of_isUpper (c : Char) (h : c.isUpper = true) : c.isAlpha = true := by
  simp [Char.isAlpha]
  exact Or.inr h

-- LLM HELPER
lemma swapCase_preserves_alpha (c : Char) : c.isAlpha = true → (swapCase c).isAlpha = true := by
  intro h
  simp [swapCase]
  by_cases h1 : c.isLower = true
  · simp [h1]
    apply isAlpha_of_isUpper
    simp [Char.toUpper, Char.isUpper]
  · by_cases h2 : c.isUpper = true
    · simp [h1, h2]
      apply isAlpha_of_isLower
      simp [Char.toLower, Char.isLower]
    · simp [h1, h2]
      exact h

-- LLM HELPER
lemma swapCase_correct_lower (c : Char) (h : c.isLower = true) : swapCase c = c.toUpper := by
  simp [swapCase, h]

-- LLM HELPER
lemma swapCase_correct_upper (c : Char) (h : c.isUpper = true) : swapCase c = c.toLower := by
  simp [swapCase]
  by_cases h2 : c.isLower = true
  · have : c.isLower = true ∧ c.isUpper = true := ⟨h2, h⟩
    have : ¬(c.isLower = true ∧ c.isUpper = true) := by
      simp [Char.isLower, Char.isUpper]
      intro hl hu
      omega
    exact absurd ⟨h2, h⟩ this
  · simp [h2, h]

-- LLM HELPER
lemma swapCase_correct_non_alpha (c : Char) (h : c.isAlpha = false) : swapCase c = c := by
  simp [swapCase]
  have h1 : c.isLower = false := by
    by_contra hl
    simp at hl
    have : c.isAlpha = true := isAlpha_of_isLower c hl
    rw [h] at this
    simp at this
  have h2 : c.isUpper = false := by
    by_contra hu
    simp at hu
    have : c.isAlpha = true := isAlpha_of_isUpper c hu
    rw [h] at this
    simp at this
  simp [h1, h2]

-- LLM HELPER
lemma map_length (s : String) (f : Char → Char) : (s.map f).length = s.length := by
  rw [String.map]
  simp

-- LLM HELPER
lemma reverse_asString_toList (s : String) : s.toList.reverse.asString.toList = s.toList.reverse := by
  exact List.toList_asString _

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · -- Case: no alphabetic characters
      constructor
      · rw [String.length, List.length_reverse, ← String.length]
      · constructor
        · intro _
          exact reverse_asString_toList s
        · intro hcontra
          simp at hcontra
          exact hcontra h
    · -- Case: has alphabetic characters
      constructor
      · exact map_length s swapCase
      · constructor
        · intro hcontra
          simp at hcontra
          have : s.all (fun c => ¬c.isAlpha) = true := by
            simp [String.all]
            exact hcontra
          exact h this
        · intro _ i hi
          rw [String.get!_map]
          let c := s.get! ⟨i⟩
          constructor
          · intro halpha
            by_cases hcase : c.isLower = true
            · left
              constructor
              · exact hcase
              · exact swapCase_correct_lower c hcase
            · right
              have hupper : c.isUpper = true := by
                simp [Char.isAlpha] at halpha
                cases' halpha with h1 h2
                · exact absurd h1 (by simp [hcase])
                · exact h2
              constructor
              · exact hupper
              · exact swapCase_correct_upper c hupper
          · intro hnotletter
            exact swapCase_correct_non_alpha c hnotletter

-- #test implementation "1234" = "4321"
-- #test implementation "ab" = "AB"
-- #test implementation "#a@C" = "#A@c"