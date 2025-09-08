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
lemma swapCase_preserves_alpha (c : Char) : c.isAlpha → (swapCase c).isAlpha := by
  intro h
  simp [swapCase]
  by_cases h1 : c.isLower
  · simp [h1]
    exact Char.isAlpha_toUpper
  · by_cases h2 : c.isUpper
    · simp [h1, h2]
      exact Char.isAlpha_toLower
    · simp [h1, h2]
      exact h

-- LLM HELPER
lemma swapCase_correct_lower (c : Char) (h : c.isLower) : swapCase c = c.toUpper := by
  simp [swapCase, h]

-- LLM HELPER
lemma swapCase_correct_upper (c : Char) (h : c.isUpper) : swapCase c = c.toLower := by
  simp [swapCase, h]
  by_cases h2 : c.isLower
  · -- A character cannot be both upper and lower
    have : ¬(c.isUpper ∧ c.isLower) := Char.not_isUpper_and_isLower
    exact absurd ⟨h, h2⟩ this
  · simp [h2]

-- LLM HELPER
lemma swapCase_correct_non_alpha (c : Char) (h : ¬c.isAlpha) : swapCase c = c := by
  simp [swapCase]
  have h1 : ¬c.isLower := fun hl => h (Char.isAlpha_iff_isLower_or_isUpper.mpr (Or.inl hl))
  have h2 : ¬c.isUpper := fun hu => h (Char.isAlpha_iff_isLower_or_isUpper.mpr (Or.inr hu))
  simp [h1, h2]

-- LLM HELPER
lemma map_length (s : String) (f : Char → Char) : (s.map f).length = s.length := by
  simp [String.length, String.map]

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
      · simp [String.length_toList]
      · constructor
        · intro _
          exact reverse_asString_toList s
        · intro hcontra
          exact absurd h hcontra
    · -- Case: has alphabetic characters
      constructor
      · exact map_length s swapCase
      · constructor
        · intro hcontra
          exact absurd hcontra h
        · intro _ i hi
          simp [String.get!_map]
          let c := s.get! ⟨i⟩
          constructor
          · intro halpha
            by_cases hcase : c.isLower
            · left
              constructor
              · exact hcase
              · exact swapCase_correct_lower c hcase
            · right
              have hupper : c.isUpper := by
                cases' Char.isAlpha_iff_isLower_or_isUpper.mp halpha with h1 h2
                · exact absurd h1 hcase
                · exact h2
              constructor
              · exact hupper
              · exact swapCase_correct_upper c hupper
          · intro hnotletter
            exact swapCase_correct_non_alpha c hnotletter

-- #test implementation "1234" = "4321"
-- #test implementation "ab" = "AB"
-- #test implementation "#a@C" = "#A@c"