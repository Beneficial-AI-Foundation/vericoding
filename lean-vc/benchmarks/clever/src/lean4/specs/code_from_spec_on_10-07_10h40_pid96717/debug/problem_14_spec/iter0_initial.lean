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
def string_prefixes_aux (s : String) (n : Nat) : List String :=
  if n = 0 then []
  else string_prefixes_aux s (n - 1) ++ [s.take n]

def implementation (string: String) : List String := string_prefixes_aux string string.length

-- LLM HELPER
lemma string_prefixes_aux_length (s : String) (n : Nat) : 
  (string_prefixes_aux s n).length = n := by
  induction n with
  | zero => simp [string_prefixes_aux]
  | succ n ih => 
    simp [string_prefixes_aux]
    rw [List.length_append, List.length_cons, List.length_nil]
    simp [ih]

-- LLM HELPER
lemma string_prefixes_aux_get (s : String) (n : Nat) (i : Nat) (h : i < n) :
  (string_prefixes_aux s n)[i]! = s.take (i + 1) := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    simp [string_prefixes_aux]
    by_cases h' : i < n
    · rw [List.getElem!_append_left]
      · exact ih h'
      · rw [string_prefixes_aux_length]
        exact h'
    · have : i = n := by
        cases' Nat.lt_succ_iff.mp h with h1 h2
        · exact absurd h1 h'
        · exact h2
      rw [this]
      rw [List.getElem!_append_right]
      · simp [List.getElem!_cons_zero]
      · rw [string_prefixes_aux_length]
        simp

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  simp
  constructor
  · exact string_prefixes_aux_length string string.length
  · intro i hi
    exact string_prefixes_aux_get string string.length i hi