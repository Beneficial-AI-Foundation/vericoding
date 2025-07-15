-- LLM HELPER
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
let factorial := factorial n;
(0 < n → result / factorial = impl (n - 1)) ∧
(n = 0 → result = 1);
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

def implementation (n: Nat) : Nat := factorial n

-- LLM HELPER
lemma factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial]; exact Nat.mul_pos (Nat.succ_pos _) ih

-- LLM HELPER
lemma factorial_div_prev (n : Nat) (h : 0 < n) : factorial n / factorial (n - 1) = n := by
  cases' n with n'
  · contradiction
  · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [factorial]
    rw [Nat.mul_div_cancel_left]
    exact factorial_pos n'

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use factorial n
  constructor
  · rfl
  · constructor
    · intro h
      rw [factorial_div_prev n h]
    · intro h
      rw [h, factorial]