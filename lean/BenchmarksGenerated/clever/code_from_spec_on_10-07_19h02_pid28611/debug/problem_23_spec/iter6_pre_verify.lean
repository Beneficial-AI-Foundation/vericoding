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
  rw [String.isEmpty]
  simp only [String.length]
  rfl

-- LLM HELPER
lemma string_length_drop_one (s: String) (h: 0 < s.length) : s.length - 1 = (s.drop 1).length := by
  rw [String.drop, String.length]
  simp only [String.length]
  have h_pos : 0 < s.data.length := h
  cases' s.data with head tail
  · simp at h_pos
  · simp [List.drop, List.length]
    rw [Nat.add_succ_sub_one, Nat.add_zero]

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
        rw [string_length_zero_iff_empty string]
        exact h
      · intro h_pos
        exact string_length_drop_one string h_pos
    · intro h
      have h_empty := h.1
      rw [← string_length_zero_iff_empty string]
      exact h_empty