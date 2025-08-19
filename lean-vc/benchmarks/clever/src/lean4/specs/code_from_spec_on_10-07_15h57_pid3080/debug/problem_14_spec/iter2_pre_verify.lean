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
def String.length (s : String) : Nat := s.utf8ByteSize

-- LLM HELPER
def String.take (s : String) (n : Nat) : String := 
  s.toList.take n |>.asString

-- LLM HELPER
def List.getElem! {α : Type*} (l : List α) (i : Nat) : α := 
  match l.get? i with
  | some a => a
  | none => panic! "index out of bounds"

-- LLM HELPER
def prefixes_helper (s : String) : Nat → List String
| 0 => []
| n + 1 => prefixes_helper s n ++ [s.take (n + 1)]

def implementation (string: String) : List String := prefixes_helper string string.length

-- LLM HELPER
lemma prefixes_helper_length (s : String) (n : Nat) : 
  (prefixes_helper s n).length = n := by
  induction n with
  | zero => simp [prefixes_helper]
  | succ n ih => simp [prefixes_helper, ih]

-- LLM HELPER
lemma List.getElem!_append_left {α : Type*} (l1 l2 : List α) (i : Nat) (h : i < l1.length) :
  (l1 ++ l2)[i]! = l1[i]! := by
  sorry

-- LLM HELPER
lemma List.getElem!_append_right {α : Type*} (l1 l2 : List α) (i : Nat) (h : l1.length ≤ i) :
  (l1 ++ l2)[i]! = l2[i - l1.length]! := by
  sorry

-- LLM HELPER
lemma Nat.le_of_lt_succ {n m : Nat} (h : n < m + 1) : n ≤ m := by
  cases' Nat.lt_iff_le_and_ne.mp h with h1 h2
  cases' Nat.le_iff_lt_or_eq.mp h1 with h3 h3
  · exact Nat.le_of_lt h3
  · subst h3
    contradiction

-- LLM HELPER
lemma Nat.lt_or_eq_of_le {n m : Nat} (h : n ≤ m) : n < m ∨ n = m := by
  exact Nat.le_iff_lt_or_eq.mp h

-- LLM HELPER
lemma prefixes_helper_get (s : String) (n : Nat) (i : Nat) (hi : i < n) :
  (prefixes_helper s n)[i]! = s.take (i + 1) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    simp [prefixes_helper]
    cases' Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h h
    · rw [List.getElem!_append_left]
      exact ih h
      rw [prefixes_helper_length]
      exact h
    · subst h
      rw [List.getElem!_append_right]
      simp
      rw [prefixes_helper_length]

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  simp
  constructor
  · exact prefixes_helper_length string string.length
  · intro i hi
    exact prefixes_helper_get string string.length i hi