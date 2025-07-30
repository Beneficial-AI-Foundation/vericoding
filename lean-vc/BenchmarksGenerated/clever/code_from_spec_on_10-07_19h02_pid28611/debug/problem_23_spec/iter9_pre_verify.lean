import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
-- every character in the string is counted once
result = 0 ↔ string.isEmpty ∧
(0 < result → result - 1 = implementation (string.drop 1))
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String): Nat := string.length

-- LLM HELPER
lemma string_length_zero_iff_empty (s: String) : s.length = 0 ↔ s.isEmpty := by
  rw [String.isEmpty, String.length, String.endPos]
  simp only [String.utf8ByteSize]
  constructor
  · intro h
    rw [← String.utf8ByteSize_eq_zero_iff] at h
    exact h
  · intro h
    rw [String.utf8ByteSize_eq_zero_iff] at h
    exact h

-- LLM HELPER
lemma string_length_drop_one (s: String) (h: 0 < s.length) : s.length - 1 = (s.drop 1).length := by
  rw [String.length, String.drop, String.length]
  simp only [String.length, String.endPos]
  have h_pos : 0 < s.data.length := by
    rw [← String.length_eq_data_length] at h
    exact h
  cases' s.data with head tail
  · simp at h_pos
  · simp [List.drop, List.length, String.mk_data]
    rw [← String.length_eq_data_length, ← String.length_eq_data_length]
    rw [String.mk_data, String.length]
    simp only [List.length]
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec implementation
  use string.length
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        rw [string_length_zero_iff_empty string] at h
        exact h
      · intro h
        rw [string_length_zero_iff_empty string]
        exact h
    · intro h
      exact string_length_drop_one string h