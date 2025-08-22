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
lemma factorial_div_self (n : Nat) (h : 0 < n) : Nat.factorial n / Nat.factorial n = 1 := by
  rw [Nat.div_self (Nat.factorial_pos n)]

-- LLM HELPER
lemma factorial_succ_div (n : Nat) : Nat.factorial (n + 1) / Nat.factorial (n + 1) = 1 := by
  rw [Nat.div_self (Nat.factorial_pos (n + 1))]

-- LLM HELPER
lemma factorial_zero : Nat.factorial 0 = 1 := by
  rfl

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use Nat.factorial n
  constructor
  · rfl
  · constructor
    · intro h
      cases' n with n'
      · contradiction
      · simp [factorial_div_self, h]
    · intro h
      rw [h]
      rfl