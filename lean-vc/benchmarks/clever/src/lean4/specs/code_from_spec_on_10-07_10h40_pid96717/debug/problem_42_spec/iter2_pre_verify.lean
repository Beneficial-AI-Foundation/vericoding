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
  (result.length = numbers.length) ∧
  ∀ i, i < numbers.length →
  result[i]! = numbers[i]! + 1
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Int) : List Int := numbers.map (· + 1)

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER
lemma list_map_get {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.map]
    | succ i' => 
      simp [List.map]
      apply ih
      simp at h
      exact Nat.lt_of_succ_lt_succ h

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use numbers.map (· + 1)
  constructor
  · rfl
  · constructor
    · exact list_map_length (· + 1) numbers
    · intro i hi
      exact list_map_get (· + 1) numbers i hi