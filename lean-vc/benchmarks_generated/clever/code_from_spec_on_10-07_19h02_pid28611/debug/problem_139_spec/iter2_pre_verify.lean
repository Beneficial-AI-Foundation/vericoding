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

def implementation (n: Nat) : Nat := 
  if n = 0 then 1 else n * implementation (n - 1)

-- LLM HELPER
lemma implementation_eq_factorial (n : Nat) : implementation n = Nat.factorial n := by
  induction n with
  | zero => simp [implementation, Nat.factorial]
  | succ n ih => 
    simp [implementation, Nat.factorial]
    rw [ih]

-- LLM HELPER
lemma factorial_div_self (n : Nat) (h : 0 < n) : Nat.factorial n / Nat.factorial n = 1 := by
  rw [Nat.div_self (Nat.factorial_pos n)]

-- LLM HELPER
lemma factorial_zero : Nat.factorial 0 = 1 := by
  rfl

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · constructor
    · intro h
      cases' n with n'
      · contradiction
      · simp [implementation_eq_factorial]
        rw [Nat.factorial_succ, Nat.mul_div_cancel_left]
        rw [implementation_eq_factorial]
        exact Nat.factorial_pos n'
    · intro h
      rw [h]
      simp [implementation]