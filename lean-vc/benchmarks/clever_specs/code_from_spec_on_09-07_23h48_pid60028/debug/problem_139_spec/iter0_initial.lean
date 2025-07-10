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
lemma factorial_div_factorial (n : Nat) (h : 0 < n) : Nat.factorial n / Nat.factorial n = 1 := by
  rw [Nat.div_self]
  exact Nat.factorial_pos n

-- LLM HELPER
lemma factorial_succ (n : Nat) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  rw [Nat.factorial_succ]

-- LLM HELPER
lemma factorial_div_prev (n : Nat) (h : 0 < n) : Nat.factorial n / Nat.factorial (n - 1) = n := by
  cases' n with n'
  · contradiction
  · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [Nat.factorial_succ]
    rw [Nat.mul_div_cancel_left]
    exact Nat.factorial_pos n'

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use Nat.factorial n
  constructor
  · rfl
  · unfold problem_spec
    constructor
    · intro h
      rw [factorial_div_prev n h]
    · intro h
      rw [h]
      rfl