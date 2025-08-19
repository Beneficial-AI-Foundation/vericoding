import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def swapCase_char (c : Char) : Char :=
  if c.isUpper then c.toLower
  else if c.isLower then c.toUpper
  else c

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
-- spec
let spec (result: String) :=
let chars_in_result := result.toList;
let chars_in_string := string.toList;
chars_in_result.length = string.length ∧
(∀ i, i < chars_in_result.length →
  let c := chars_in_result.get! i;
  let c' := chars_in_string.get! i;
  (c.isUpper → c'.isLower) ∧
  (c.isLower → c'.isUpper) ∧
  ((¬ c.isUpper ∧ ¬ c.isLower) → c = c')
);
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : String := 
  String.mk (string.toList.map swapCase_char)

-- LLM HELPER
lemma swapCase_char_preserves_property (c : Char) :
  let c' := swapCase_char c
  (c'.isUpper → c.isLower) ∧
  (c'.isLower → c.isUpper) ∧
  ((¬ c'.isUpper ∧ ¬ c'.isLower) → c' = c) := by
  simp [swapCase_char]
  split_ifs with h1 h2
  · constructor
    · intro h
      simp [Char.isUpper_toLower] at h
    · constructor
      · intro h
        exact h1
      · intro h
        simp [Char.isUpper_toLower, Char.isLower_toLower] at h
  · constructor
    · intro h
      exact h2
    · constructor
      · intro h
        simp [Char.isLower_toUpper] at h
      · intro h
        simp [Char.isUpper_toUpper, Char.isLower_toUpper] at h
  · constructor
    · intro h
      by_contra
      exact h h1
    · constructor
      · intro h
        by_contra
        exact h h2
      · intro h
        rfl

-- LLM HELPER
lemma toList_map_length (s : String) (f : Char → Char) :
  (String.mk (s.toList.map f)).toList.length = s.toList.length := by
  simp [String.toList_mk]

-- LLM HELPER
lemma toList_map_get (s : String) (f : Char → Char) (i : Nat) (h : i < s.toList.length) :
  (String.mk (s.toList.map f)).toList.get! i = f (s.toList.get! i) := by
  simp [String.toList_mk]
  rw [List.get!_map]

theorem correctness
(string: String)
: problem_spec implementation string := by
  simp [problem_spec, implementation]
  use String.mk (string.toList.map swapCase_char)
  constructor
  · rfl
  · constructor
    · simp [String.length_eq]
      exact toList_map_length string swapCase_char
    · intro i hi
      rw [toList_map_get string swapCase_char i]
      exact swapCase_char_preserves_property (string.toList.get! i)
      rw [toList_map_length] at hi
      exact hi