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
lemma factorial_succ_div (n : Nat) : Nat.factorial (n + 1) / Nat.factorial n = n + 1 := by
  rw [Nat.factorial_succ]
  rw [Nat.mul_div_cancel_left (Nat.factorial n) (Nat.succ_pos n)]

-- LLM HELPER
lemma factorial_zero : Nat.factorial 0 = 1 := by
  rfl

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use Nat.factorial n
  constructor
  · rfl
  · unfold implementation
    constructor
    · intro h
      cases' n with n'
      · contradiction
      · simp [Nat.factorial_succ]
        rw [Nat.mul_div_cancel_left (Nat.factorial n') (Nat.succ_pos n')]
        rfl
    · intro h
      rw [h]
      rfl