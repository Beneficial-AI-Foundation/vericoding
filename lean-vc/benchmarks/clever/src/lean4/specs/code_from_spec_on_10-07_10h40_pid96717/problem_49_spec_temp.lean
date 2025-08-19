import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat → Nat)
-- inputs
(n p: Nat) :=
-- spec
let spec (result: Nat) :=
0 < p ∧
result < p ∧
(∃ k : Nat, p * k + result = Nat.pow 2 n)
-- program termination
∃ result, implementation n p = result ∧
spec result

def implementation (n p: Nat) : Nat := (2^n) % p

-- LLM HELPER
lemma nat_pos_of_ne_zero {n : Nat} (h : n ≠ 0) : 0 < n := by
  cases' n with n
  · contradiction
  · exact Nat.zero_lt_succ n

-- LLM HELPER
lemma nat_mod_lt (a b : Nat) (hb : 0 < b) : a % b < b := by
  exact Nat.mod_lt a hb

-- LLM HELPER
lemma nat_div_add_mod (a b : Nat) : b * (a / b) + a % b = a := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod a b

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  unfold problem_spec
  simp only [implementation]
  use (2^n) % p
  constructor
  · rfl
  · by_cases h : p = 0
    · simp [h]
      constructor
      · rw [h]
        exact Nat.one_pos
      constructor
      · rw [h]
        simp
        exact Nat.zero_lt_one
      · use 0
        rw [h]
        simp
    · have hp : 0 < p := nat_pos_of_ne_zero h
      constructor
      · exact hp
      constructor
      · exact nat_mod_lt (2^n) p hp
      · use (2^n) / p
        exact nat_div_add_mod (2^n) p