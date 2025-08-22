import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → List Int)
(numbers: List Int) :=
let spec (result: List Int) :=
  result.length = numbers.length ∧
  ∀ i, i < numbers.length →
    result[i]! = numbers[i]! * 2
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Int) : List Int := numbers.map (· * 2)

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER
lemma map_get {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]'(by rw [map_length]; exact h) = f (l[i]'h) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.map, List.get]
    | succ j =>
      simp [List.map, List.get]
      apply ih
      simp at h
      exact Nat.lt_of_succ_lt_succ h

-- LLM HELPER
lemma map_getElem {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]! = f (l[i]!) := by
  simp [List.getElem!]
  have h' : i < (l.map f).length := by rw [map_length]; exact h
  rw [List.getElem_map]

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use numbers.map (· * 2)
  constructor
  · rfl
  · constructor
    · exact map_length (· * 2) numbers
    · intro i hi
      rw [map_getElem]
      ring