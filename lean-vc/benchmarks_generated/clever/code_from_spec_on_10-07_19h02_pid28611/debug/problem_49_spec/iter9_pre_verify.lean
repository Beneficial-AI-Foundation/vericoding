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

def implementation (n p: Nat) : Nat := if p = 0 then 0 else (2^n) % p

-- LLM HELPER
lemma mod_lt_of_pos (a b : Nat) (h : 0 < b) : a % b < b := Nat.mod_lt a h

-- LLM HELPER
lemma div_add_mod_eq_pow (n p : Nat) (h : 0 < p) : p * (2^n / p) + 2^n % p = Nat.pow 2 n := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod (2^n) p

-- LLM HELPER
lemma pos_p_case (n p : Nat) (h : 0 < p) : problem_spec implementation n p := by
  unfold problem_spec implementation
  simp only [exists_prop]
  use (2^n) % p
  constructor
  · simp [h]
  · constructor
    · exact h
    · constructor
      · exact mod_lt_of_pos (2^n) p h
      · use (2^n) / p
        exact div_add_mod_eq_pow n p h

-- LLM HELPER
lemma zero_p_case (n : Nat) : ¬(0 < 0 ∧ ∃ result, result < 0 ∧ ∃ k : Nat, 0 * k + result = Nat.pow 2 n) := by
  intro h
  exact Nat.lt_irrefl 0 h.1

theorem correctness
(n p: Nat)
: problem_spec implementation n p
:= by
  by_cases h : 0 < p
  · exact pos_p_case n p h
  · push_neg at h
    simp at h
    subst h
    unfold problem_spec implementation
    simp only [exists_prop]
    use 0
    constructor
    · simp
    · exact zero_p_case n