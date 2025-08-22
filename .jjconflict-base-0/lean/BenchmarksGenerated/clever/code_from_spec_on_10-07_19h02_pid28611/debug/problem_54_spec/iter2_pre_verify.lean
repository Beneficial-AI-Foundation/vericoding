import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(s0 s1: String) :=
-- spec
let spec (res: Bool) :=
  res ↔ (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList)
-- program terminates
∃ result, impl s0 s1 = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

-- LLM HELPER
def char_set_equal (s0 s1: String) : Bool :=
  s0.toList.all (fun c => c ∈ s1.toList) && s1.toList.all (fun c => c ∈ s0.toList)

def implementation (s0 s1: String) : Bool := char_set_equal s0 s1

-- LLM HELPER
lemma char_set_equal_correct (s0 s1: String) :
  char_set_equal s0 s1 ↔ (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList) := by
  simp [char_set_equal]
  constructor
  · intro h c
    cases' h with h1 h2
    rw [List.all_eq_true] at h1 h2
    constructor
    · intro hc
      exact h1 c hc
    · intro hc
      exact h2 c hc
  · intro h
    constructor
    · rw [List.all_eq_true]
      intro c hc
      exact (h c).mp hc
    · rw [List.all_eq_true]
      intro c hc
      exact (h c).mpr hc

theorem correctness
(s0 s1: String)
: problem_spec implementation s0 s1  := by
  simp [problem_spec, implementation]
  exact char_set_equal_correct s0 s1