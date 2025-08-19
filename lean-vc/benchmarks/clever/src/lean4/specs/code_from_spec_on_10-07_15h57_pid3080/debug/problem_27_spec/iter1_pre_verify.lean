import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

-- LLM HELPER
def swapCase (c : Char) : Char :=
  if c.isUpper then c.toLower
  else if c.isLower then c.toUpper
  else c

def implementation (string: String) : String := 
  String.mk (string.toList.map swapCase)

-- LLM HELPER
lemma swapCase_preserves_length (s : String) : 
  (String.mk (s.toList.map swapCase)).toList.length = s.length := by
  simp [String.toList_mk, List.length_map]

-- LLM HELPER
lemma swapCase_correct (c : Char) : 
  let c' := swapCase c
  (c'.isUpper → c.isLower) ∧
  (c'.isLower → c.isUpper) ∧
  ((¬ c'.isUpper ∧ ¬ c'.isLower) → c' = c) := by
  simp [swapCase]
  by_cases h1 : c.isUpper
  · simp [h1]
    constructor
    · intro h
      simp [Char.isUpper_toLower] at h
    · constructor
      · intro h
        simp [Char.isLower_toLower] at h
        exact Char.isUpper_iff_isLower.mp h1
      · intro h
        simp [Char.isUpper_toLower, Char.isLower_toLower] at h
  · by_cases h2 : c.isLower
    · simp [h1, h2]
      constructor
      · intro h
        simp [Char.isUpper_toUpper] at h
        exact Char.isLower_iff_isUpper.mp h2
      · constructor
        · intro h
          simp [Char.isLower_toUpper] at h
        · intro h
          simp [Char.isUpper_toUpper, Char.isLower_toUpper] at h
    · simp [h1, h2]
      constructor
      · intro h
        simp [Char.isUpper] at h1 h
        exact False.elim (h1 h)
      · constructor
        · intro h
          simp [Char.isLower] at h2 h
          exact False.elim (h2 h)
        · intro h
          rfl

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  simp
  let result := String.mk (string.toList.map swapCase)
  use result
  simp
  constructor
  · exact swapCase_preserves_length string
  · intro i hi
    simp [String.toList_mk] at hi ⊢
    rw [List.get!_map]
    exact swapCase_correct (string.toList.get! i)