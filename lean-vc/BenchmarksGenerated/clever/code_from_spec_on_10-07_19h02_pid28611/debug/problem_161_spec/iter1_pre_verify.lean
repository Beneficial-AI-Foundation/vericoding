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
def toggleCase (c : Char) : Char :=
  if c.isLower then c.toUpper
  else if c.isUpper then c.toLower
  else c

-- LLM HELPER
def processString (s : String) : String :=
  if s.all (λ c => not (c.isAlpha)) then
    ⟨s.toList.reverse⟩
  else
    ⟨s.toList.map toggleCase⟩

def implementation (s: String) : String := processString s

-- LLM HELPER
lemma String.get_mk_list (l : List Char) (i : Fin l.length) :
  (⟨l⟩ : String).get ⟨i.val, by simp; exact i.isLt⟩ = l.get i := by
  rfl

-- LLM HELPER
lemma String.length_mk_list (l : List Char) : (⟨l⟩ : String).length = l.length := by
  rfl

-- LLM HELPER
lemma String.toList_mk_list (l : List Char) : (⟨l⟩ : String).toList = l := by
  rfl

-- LLM HELPER
lemma List.get_reverse (l : List α) (i : Fin l.length) :
  l.reverse.get ⟨l.length - 1 - i.val, by
    simp [List.length_reverse]
    omega⟩ = l.get ⟨l.length - 1 - i.val, by omega⟩ := by
  rw [List.get_reverse']
  congr

-- LLM HELPER
lemma List.get_map (l : List α) (f : α → β) (i : Fin l.length) :
  (l.map f).get ⟨i.val, by simp; exact i.isLt⟩ = f (l.get i) := by
  rw [List.get_map]

-- LLM HELPER
lemma toggleCase_spec (c : Char) :
  (c.isAlpha → ((c.isLower → c.toUpper = toggleCase c) ∨
              (c.isUpper → c.toLower = toggleCase c))) ∧
  (¬ c.isAlpha → c = toggleCase c) := by
  constructor
  · intro h_alpha
    unfold toggleCase
    by_cases h_lower : c.isLower
    · left
      intro
      simp [h_lower]
    · right
      intro h_upper
      simp [h_lower, h_upper]
  · intro h_not_alpha
    unfold toggleCase
    by_cases h_lower : c.isLower
    · have : c.isAlpha := Char.isAlpha_of_isLower h_lower
      contradiction
    · by_cases h_upper : c.isUpper
      · have : c.isAlpha := Char.isAlpha_of_isUpper h_upper
        contradiction
      · simp [h_lower, h_upper]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation processString
  split_ifs with h
  · -- Case: no alphabetic characters
    use ⟨s.toList.reverse⟩
    constructor
    · rfl
    · constructor
      · -- Length preservation
        simp [String.length_mk_list, List.length_reverse]
      · constructor
        · -- If no alphabet, result is reverse
          intro h_no_alpha
          simp [String.toList_mk_list]
        · -- If has alphabet (contradiction)
          intro h_has_alpha
          exfalso
          exact h_has_alpha h
  · -- Case: has alphabetic characters
    use ⟨s.toList.map toggleCase⟩
    constructor
    · rfl
    · constructor
      · -- Length preservation
        simp [String.length_mk_list, List.length_map]
      · constructor
        · -- If no alphabet (contradiction)
          intro h_no_alpha
          exfalso
          exact h h_no_alpha
        · -- If has alphabet, toggle case
          intro h_has_alpha i h_i_lt
          have h_i_lt_map : i < (s.toList.map toggleCase).length := by
            simp [List.length_map]
            exact h_i_lt
          have h_get_orig : s.get! ⟨i⟩ = s.toList.get ⟨i, h_i_lt⟩ := by
            rw [String.get!_eq_get]
            congr
          have h_get_result : (⟨s.toList.map toggleCase⟩ : String).get! ⟨i⟩ = 
                             (s.toList.map toggleCase).get ⟨i, h_i_lt_map⟩ := by
            rw [String.get!_eq_get]
            congr
            simp [String.length_mk_list, List.length_map]
          rw [h_get_orig, h_get_result]
          rw [List.get_map]
          exact toggleCase_spec (s.toList.get ⟨i, h_i_lt⟩)