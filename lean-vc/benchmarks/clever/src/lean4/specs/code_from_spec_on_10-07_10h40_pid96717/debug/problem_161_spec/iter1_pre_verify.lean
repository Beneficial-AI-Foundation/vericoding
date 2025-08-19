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
def swapCase (c: Char) : Char :=
if c.isLower then c.toUpper
else if c.isUpper then c.toLower
else c

-- LLM HELPER
def processString (s: String) : String :=
if s.all (λ c => not (c.isAlpha)) then
  String.mk s.toList.reverse
else
  String.mk (s.toList.map swapCase)

def implementation (s: String) : String := processString s

-- LLM HELPER
lemma swapCase_preserves_non_alpha (c: Char) (h: ¬c.isAlpha) : swapCase c = c := by
  simp [swapCase]
  simp [Char.isAlpha] at h
  cases' Char.isLower c with
  · simp
    cases' Char.isUpper c with
    · simp
    · simp at h
  · simp at h

-- LLM HELPER
lemma swapCase_correct_lower (c: Char) (h: c.isLower) : swapCase c = c.toUpper := by
  simp [swapCase, h]

-- LLM HELPER
lemma swapCase_correct_upper (c: Char) (h: c.isUpper) : swapCase c = c.toLower := by
  simp [swapCase]
  simp [h]
  simp [Char.isLower]
  exact Char.isLower_toUpper_iff.mpr h

-- LLM HELPER
lemma processString_length (s: String) : (processString s).length = s.length := by
  simp [processString]
  split_ifs with h
  · simp [String.length_mk]
  · simp [String.length_mk, List.length_map]

-- LLM HELPER
lemma processString_no_alpha_case (s: String) (h: s.all (λ c => not (c.isAlpha))) :
  (processString s).toList = s.toList.reverse := by
  simp [processString, h]

-- LLM HELPER
lemma processString_has_alpha_case (s: String) (h: s.all (λ c => not (c.isAlpha)) = false) :
  ∀ i, i < s.length →
  let c := s.get! ⟨i⟩
  (c.isAlpha → ((c.isLower → c.toUpper = (processString s).get! ⟨i⟩) ∨
              (c.isUpper → c.toLower = (processString s).get! ⟨i⟩))) ∧
  (¬ c.isAlpha → c = (processString s).get! ⟨i⟩) := by
  intro i hi
  simp [processString, h]
  let c := s.get! ⟨i⟩
  constructor
  · intro hAlpha
    simp [String.get!_mk]
    have : i < (s.toList.map swapCase).length := by simp [List.length_map, String.length_toList.symm, hi]
    simp [List.get!_map, this]
    cases' c.isLower with
    · left
      intro hLower
      exact swapCase_correct_lower c hLower
    · right
      intro hUpper
      exact swapCase_correct_upper c hUpper
  · intro hNotAlpha
    simp [String.get!_mk]
    have : i < (s.toList.map swapCase).length := by simp [List.length_map, String.length_toList.symm, hi]
    simp [List.get!_map, this]
    exact swapCase_preserves_non_alpha c hNotAlpha

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  use processString s
  constructor
  · rfl
  · constructor
    · exact processString_length s
    · constructor
      · intro h
        exact processString_no_alpha_case s h
      · intro h
        exact processString_has_alpha_case s h