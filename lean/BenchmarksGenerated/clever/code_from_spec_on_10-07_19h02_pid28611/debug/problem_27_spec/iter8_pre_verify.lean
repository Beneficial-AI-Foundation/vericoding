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
  if c.isLower then c.toUpper else if c.isUpper then c.toLower else c

def implementation (string: String) : String := 
  ⟨string.toList.map swapCase⟩

-- LLM HELPER
lemma swapCase_property (c : Char) : 
  let c' := swapCase c
  (c'.isUpper → c.isLower) ∧ (c'.isLower → c.isUpper) ∧ ((¬ c'.isUpper ∧ ¬ c'.isLower) → c' = c) := by
  unfold swapCase
  by_cases h1 : c.isLower
  · simp [h1]
    constructor
    · intro h
      exact h1
    · constructor
      · intro h
        have : c.toUpper.isLower = false := Char.not_isLower_toUpper c
        rw [this] at h
        exact False.elim h
      · intro h
        have : c.toUpper.isUpper = true := Char.isUpper_toUpper c
        rw [this] at h
        exact False.elim (h.1 rfl)
  · by_cases h2 : c.isUpper
    · simp [h1, h2]
      constructor
      · intro h
        have : c.toLower.isUpper = false := Char.not_isUpper_toLower c
        rw [this] at h
        exact False.elim h
      · constructor
        · intro h
          exact h2
        · intro h
          have : c.toLower.isLower = true := Char.isLower_toLower c
          rw [this] at h
          exact False.elim (h.2 rfl)
    · simp [h1, h2]
      intro h
      rfl

-- LLM HELPER
lemma string_toList_mk (chars : List Char) : (⟨chars⟩ : String).toList = chars := by
  rfl

-- LLM HELPER
lemma list_get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) :
  i < (l.map f).length → (l.map f).get! i = f (l.get! i) := by
  intro h
  have h' : i < l.length := by
    rw [List.length_map] at h
    exact h
  rw [List.get!_eq_get _ h, List.get!_eq_get _ h']
  rw [List.get_map]

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  let result := implementation string
  use result
  constructor
  · rfl
  · constructor
    · simp only [implementation, string_toList_mk, List.length_map]
    · intro i hi
      simp only [implementation, string_toList_mk] at hi ⊢
      rw [list_get_map swapCase (string.toList) i hi]
      exact swapCase_property (string.toList.get! i)