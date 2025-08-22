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
    String.mk s.toList.reverse
  else
    String.mk (s.toList.map toggleCase)

def implementation (s: String) : String := processString s

-- LLM HELPER
lemma String.get_mk_list (l : List Char) (i : Nat) (h : i < l.length) :
  (String.mk l).get ⟨i, by simp; exact h⟩ = l.get ⟨i, h⟩ := by
  rfl

-- LLM HELPER
lemma String.length_mk_list (l : List Char) : (String.mk l).length = l.length := by
  rfl

-- LLM HELPER
lemma String.toList_mk_list (l : List Char) : (String.mk l).toList = l := by
  rfl

-- LLM HELPER
lemma List.get_map_helper (l : List α) (f : α → β) (i : Nat) (h : i < l.length) :
  (l.map f).get ⟨i, by simp; exact h⟩ = f (l.get ⟨i, h⟩) := by
  rw [List.getElem_map]

-- LLM HELPER
lemma Char.isAlpha_of_isLower_helper (c : Char) : c.isLower → c.isAlpha := by
  intro h
  exact Char.isAlpha_of_isLower h

-- LLM HELPER
lemma Char.isAlpha_of_isUpper_helper (c : Char) : c.isUpper → c.isAlpha := by
  intro h
  exact Char.isAlpha_of_isUpper h

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
    · have : c.isAlpha := Char.isAlpha_of_isLower_helper c h_lower
      contradiction
    · by_cases h_upper : c.isUpper
      · have : c.isAlpha := Char.isAlpha_of_isUpper_helper c h_upper
        contradiction
      · simp [h_lower, h_upper]

-- LLM HELPER
lemma String.get_bang_eq_get_toList (s : String) (i : ℕ) (h : i < s.length) :
  s.get! ⟨i⟩ = s.toList.get ⟨i, by simp; exact h⟩ := by
  rw [String.get!_eq_get]
  simp

-- LLM HELPER
lemma String.get_bang_mk_map (s : String) (f : Char → Char) (i : ℕ) (h : i < s.length) :
  (String.mk (s.toList.map f)).get! ⟨i⟩ = f (s.toList.get ⟨i, by simp; exact h⟩) := by
  rw [String.get!_eq_get]
  have h_len : (String.mk (s.toList.map f)).length = s.length := by
    simp [String.length_mk_list, List.length_map]
  rw [String.get_mk_list]
  rw [List.get_map_helper]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation processString
  split_ifs with h
  · -- Case: no alphabetic characters
    use String.mk s.toList.reverse
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
    use String.mk (s.toList.map toggleCase)
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
          have h_i_lt_list : i < s.toList.length := by simp; exact h_i_lt
          have h_get_orig : s.get! ⟨i⟩ = s.toList.get ⟨i, h_i_lt_list⟩ := by
            rw [String.get!_eq_get]
            simp
          have h_get_result : (String.mk (s.toList.map toggleCase)).get! ⟨i⟩ = 
                             toggleCase (s.toList.get ⟨i, h_i_lt_list⟩) := by
            rw [String.get!_eq_get]
            have h_len : (String.mk (s.toList.map toggleCase)).length = s.length := by
              simp [String.length_mk_list, List.length_map]
            rw [String.get_mk_list]
            rw [List.get_map_helper]
          rw [h_get_orig, h_get_result]
          exact toggleCase_spec (s.toList.get ⟨i, h_i_lt_list⟩)