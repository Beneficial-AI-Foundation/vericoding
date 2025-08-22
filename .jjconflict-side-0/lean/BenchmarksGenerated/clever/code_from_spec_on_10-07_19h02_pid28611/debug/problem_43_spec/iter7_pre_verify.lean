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
lemma map_getElem_bang (f : Int → Int) (l : List Int) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]! = f (l[i]!) := by
  simp [List.getElem!]
  cases' hdec : i < (l.map f).length with
  · simp [List.get?, List.getElem?]
    rw [List.getElem?_map]
    simp [List.getElem?]
    rw [if_neg]
    simp
    rw [map_length] at hdec
    exact hdec
  · simp [List.get?, List.getElem?]
    rw [List.getElem?_map]
    simp [List.getElem?]
    rw [if_pos h]
    simp

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use numbers.map (· * 2)
  constructor
  · rfl
  constructor
  · exact map_length (· * 2) numbers
  · intro i hi
    rw [map_getElem_bang]
    exact hi