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
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.containsSubstr b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def check_rotation (a b: String) (i: Nat) : Bool :=
  let b_rotation := b.drop i ++ b.take i
  a.containsSubstr b_rotation

-- LLM HELPER
def check_all_rotations (a b: String) (i: Nat) : Bool :=
  if i >= b.length then false
  else if check_rotation a b i then true
  else check_all_rotations a b (i + 1)

def implementation (a b: String) : Bool := 
  if b.length = 0 then true
  else if b.length > a.length then false
  else check_all_rotations a b 0

-- LLM HELPER
lemma check_rotation_correct (a b: String) (i: Nat) :
  check_rotation a b i = true ↔ a.containsSubstr (b.drop i ++ b.take i) :=
by
  simp [check_rotation]

-- LLM HELPER
lemma check_all_rotations_correct (a b: String) (start: Nat) :
  check_all_rotations a b start = true ↔ 
  ∃ i : Nat, start ≤ i ∧ i < b.length ∧ a.containsSubstr (b.drop i ++ b.take i) :=
by
  induction start using Nat.strong_induction_on with
  | h start ih =>
    simp [check_all_rotations]
    by_cases h1 : start >= b.length
    · simp [h1]
      constructor
      · intro h2
        exfalso
        exact h2
      · intro ⟨i, hi1, hi2, _⟩
        omega
    · simp [h1]
      by_cases h2 : check_rotation a b start
      · simp [h2]
        constructor
        · intro
          use start
          constructor
          · omega
          · constructor
            · omega
            · rw [check_rotation_correct] at h2
              exact h2
        · intro ⟨i, hi1, hi2, hi3⟩
          trivial
      · simp [h2]
        have : start + 1 < b.length := by omega
        rw [ih (start + 1) (by omega)]
        constructor
        · intro ⟨i, hi1, hi2, hi3⟩
          use i
          constructor
          · omega
          · exact ⟨hi2, hi3⟩
        · intro ⟨i, hi1, hi2, hi3⟩
          use i
          constructor
          · omega
          · exact ⟨hi2, hi3⟩

theorem correctness
(a b: String)
: problem_spec implementation a b := 
by
  simp [problem_spec, implementation]
  use (if b.length = 0 then true else if b.length > a.length then false else check_all_rotations a b 0)
  constructor
  · rfl
  · simp
    constructor
    · intro h
      by_cases h1 : b.length = 0
      · simp [h1]
      · simp [h1] at h
        contradiction
    · intro h
      by_cases h1 : b.length = 0
      · simp [h1] at h
        contradiction
      · simp [h1]
        by_cases h2 : b.length > a.length
        · simp [h2]
          constructor
          · intro
            omega
          · intro ⟨_, _⟩
            omega
        · simp [h2]
          rw [check_all_rotations_correct]
          constructor
          · intro ⟨i, hi1, hi2, hi3⟩
            constructor
            · omega
            · use i
              exact ⟨hi2, hi3⟩
          · intro ⟨h3, i, hi1, hi2⟩
            use i
            constructor
            · omega
            · exact ⟨hi1, hi2⟩