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
    exact Nat.mul_pos (Nat.succ_pos n) ih

-- LLM HELPER
lemma factorial_div_factorial (n : Nat) (h : 0 < n) : 
  Nat.factorial n / Nat.factorial n = 1 := by
  exact Nat.div_self (ne_of_gt (factorial_pos n))

-- LLM HELPER
lemma factorial_recurrence (n : Nat) (h : 0 < n) :
  Nat.factorial n / Nat.factorial n = Nat.factorial (n - 1) := by
  cases n with
  | zero => contradiction
  | succ k =>
    simp [Nat.factorial]
    simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [Nat.mul_div_cancel_left (Nat.factorial k) (Nat.succ_pos k)]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use Nat.factorial n
  constructor
  · rfl
  · unfold implementation
    simp
    constructor
    · intro h
      cases n with
      | zero => contradiction
      | succ k =>
        simp [Nat.factorial]
        simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
        rw [Nat.mul_div_cancel_left (Nat.factorial k) (Nat.succ_pos k)]
    · intro h
      subst h
      simp [Nat.factorial]