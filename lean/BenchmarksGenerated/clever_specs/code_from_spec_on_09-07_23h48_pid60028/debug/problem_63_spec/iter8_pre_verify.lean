def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
fibonacci_non_computable_3 n result
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def fibonacci_non_computable_3 (n : Nat) (result : Nat) : Prop :=
  match n with
  | 0 => result = 0
  | 1 => result = 1
  | n + 2 => ∃ f_n f_n1, fibonacci_non_computable_3 n f_n ∧ 
                          fibonacci_non_computable_3 (n + 1) f_n1 ∧
                          result = f_n + f_n1

-- LLM HELPER
def fib_helper (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib_helper n + fib_helper (n + 1)

def implementation (n: Nat) : Nat := fib_helper n

-- LLM HELPER
lemma fib_helper_satisfies_spec (n : Nat) : fibonacci_non_computable_3 n (fib_helper n) :=
  by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      match n with
      | 0 => simp [fibonacci_non_computable_3, fib_helper]
      | 1 => simp [fibonacci_non_computable_3, fib_helper]
      | n + 2 => 
        simp [fibonacci_non_computable_3, fib_helper]
        use fib_helper n, fib_helper (n + 1)
        constructor
        · apply ih
          simp [Nat.lt_add_of_pos_right]
        constructor
        · apply ih
          simp [Nat.lt_succ_iff]
        · rfl

theorem correctness
(n: Nat)
: problem_spec implementation n :=
by
  simp [problem_spec, implementation]
  use fib_helper n
  constructor
  · rfl
  · exact fib_helper_satisfies_spec n