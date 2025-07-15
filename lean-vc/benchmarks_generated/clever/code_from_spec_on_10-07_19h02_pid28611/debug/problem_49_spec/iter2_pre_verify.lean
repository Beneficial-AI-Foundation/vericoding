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
lemma mod_lt_of_pos (a b : Nat) (h : 0 < b) : a % b < b := Nat.mod_lt a h

-- LLM HELPER
lemma mod_add_div (a b : Nat) : a % b + b * (a / b) = a := by
  rw [add_comm]
  exact Nat.div_add_mod a b

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  by_cases h : 0 < p
  · use (2^n) % p
    constructor
    · rfl
    · constructor
      · exact h
      · constructor
        · exact mod_lt_of_pos (2^n) p h
        · use (2^n) / p
          exact mod_add_div (2^n) p
  · push_neg at h
    cases' p with p'
    · exfalso
      exact Nat.not_lt_zero 0 h
    · exfalso
      apply h
      exact Nat.succ_pos p'