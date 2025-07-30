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
  | zero => 
    unfold implementation
    simp
  | succ n ih => 
    unfold implementation
    simp
    rw [Nat.factorial_succ, ih]

-- LLM HELPER
lemma factorial_div_factorial (n : Nat) (h : 0 < n) : Nat.factorial n / Nat.factorial (n - 1) = n := by
  cases' n with n'
  · contradiction
  · rw [Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.factorial_succ]
    rw [Nat.mul_div_cancel_left (Nat.factorial n') (Nat.pos_of_ne_zero (Nat.succ_ne_zero n'))]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · constructor
    · intro h
      rw [implementation_eq_factorial]
      have : Nat.factorial n / Nat.factorial (n - 1) = n := factorial_div_factorial n h
      rw [this]
      rw [implementation_eq_factorial]
    · intro h
      rw [h]
      unfold implementation
      simp