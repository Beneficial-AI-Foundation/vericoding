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

def implementation (n p: Nat) : Nat := 
  if p = 0 then 0 else (2^n) % p

-- LLM HELPER
lemma mod_lt_of_pos (a b : Nat) (h : 0 < b) : a % b < b := by
  cases' b with b
  · contradiction
  · exact Nat.mod_lt a (Nat.succ_pos b)

-- LLM HELPER
lemma div_add_mod' (a b : Nat) : b * (a / b) + a % b = a := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod a b

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  simp [problem_spec]
  use implementation n p
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · simp [h]
      constructor
      · simp [h]
      · constructor
        · simp [h]
        · use 0
          simp [h]
    · push_neg at h
      have hp : 0 < p := Nat.pos_of_ne_zero h
      constructor
      · exact hp
      · constructor
        · exact mod_lt_of_pos (2^n) p hp
        · use (2^n) / p
          exact div_add_mod' (2^n) p