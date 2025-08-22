import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(string: String) :=
-- spec
let spec (result: List String) :=
result.length = string.length ∧
∀ i, i < result.length →
result[i]! = string.take (i + 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def prefixes (s : String) : List String :=
  List.range s.length |>.map (fun i => s.take (i + 1))

def implementation (string: String) : List String := prefixes string

-- LLM HELPER
lemma prefixes_length (s : String) : (prefixes s).length = s.length := by
  simp [prefixes]

-- LLM HELPER
lemma prefixes_get (s : String) (i : Nat) (h : i < (prefixes s).length) : 
  (prefixes s)[i]! = s.take (i + 1) := by
  simp [prefixes]
  rw [List.getElem!_of_getElem?]
  rw [List.getElem?_map]
  rw [List.getElem?_range]
  simp
  rw [prefixes_length] at h
  exact h

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  simp [problem_spec, implementation]
  use prefixes string
  constructor
  · rfl
  · constructor
    · exact prefixes_length string
    · intro i hi
      exact prefixes_get string i hi