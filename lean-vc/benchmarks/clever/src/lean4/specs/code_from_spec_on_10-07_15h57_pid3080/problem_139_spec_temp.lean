import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
let factorial := Nat.factorial n;
(0 < n → result / factorial = impl (n - 1)) ∧
(n = 0 → result = 1);
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

def implementation (n: Nat) : Nat := Nat.factorial n

-- LLM HELPER
lemma factorial_pos (n : Nat) : 0 < Nat.factorial n := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih => 
    simp [Nat.factorial]
    apply Nat.mul_pos
    · simp
    · exact ih

-- LLM HELPER
lemma factorial_succ_eq (n : Nat) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  rfl

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · rfl
  · constructor
    · intro h
      cases n with
      | zero => contradiction
      | succ n' =>
        simp [factorial_succ_eq]
        rw [Nat.mul_div_cancel_left]
        rfl
        exact factorial_pos n'
    · intro h
      simp [h]