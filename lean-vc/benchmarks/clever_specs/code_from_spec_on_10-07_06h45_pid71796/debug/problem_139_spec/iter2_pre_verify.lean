-- LLM HELPER
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- LLM HELPER
lemma factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => 
    simp [factorial]
    apply Nat.mul_pos
    · simp
    · exact ih

-- LLM HELPER
lemma factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := by
  rfl

-- LLM HELPER
lemma factorial_zero : factorial 0 = 1 := by
  rfl

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

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use factorial n
  constructor
  · rfl
  · unfold implementation
    constructor
    · intro h
      cases' n with n'
      · contradiction
      · simp [factorial_succ]
        rw [Nat.mul_div_cancel_left (factorial n') (factorial_pos n')]
        rfl
    · intro h
      rw [h]
      rfl