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
  if p = 0 then 0 else Nat.pow 2 n % p

-- LLM HELPER
lemma mod_lt_of_pos (a b : Nat) (h : 0 < b) : a % b < b := by
  exact Nat.mod_lt a h

-- LLM HELPER
lemma mod_add_div (a b : Nat) : a % b + b * (a / b) = a := by
  rw [Nat.add_comm]
  exact Nat.div_add_mod a b

theorem correctness
(n p: Nat)
: problem_spec implementation n p := by
  simp [problem_spec, implementation]
  by_cases h : p = 0
  · simp [h]
    exfalso
    exact Nat.not_lt_zero 0
  · simp [h]
    constructor
    · exact Nat.pos_of_ne_zero h
    constructor
    · exact mod_lt_of_pos (Nat.pow 2 n) p (Nat.pos_of_ne_zero h)
    · use (Nat.pow 2 n) / p
      rw [Nat.mul_comm]
      exact mod_add_div (Nat.pow 2 n) p