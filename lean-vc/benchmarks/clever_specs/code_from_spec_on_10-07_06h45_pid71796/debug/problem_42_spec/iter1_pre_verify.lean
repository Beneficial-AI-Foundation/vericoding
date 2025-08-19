import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
lemma map_length (f : Int → Int) (l : List Int) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma map_getElem (f : Int → Int) (l : List Int) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp
    | succ j => 
      simp
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
    · exact map_length (· + 1) numbers
    · intro i hi
      rw [map_getElem]
      simp