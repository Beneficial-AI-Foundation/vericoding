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
lemma map_length (f : Int → Int) (l : List Int) : (l.map f).length = l.length := by
  exact List.length_map f l

-- LLM HELPER
lemma map_getElem (f : Int → Int) (l : List Int) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]! = f (l[i]!) := by
  rw [List.getElem_map]

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use numbers.map (· + 1)
  constructor
  · rfl
  · constructor
    · exact List.length_map (· + 1) numbers
    · intro i hi
      rw [List.getElem_map]
      simp