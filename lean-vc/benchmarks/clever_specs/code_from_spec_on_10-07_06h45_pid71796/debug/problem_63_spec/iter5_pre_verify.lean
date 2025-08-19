-- LLM HELPER
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

-- LLM HELPER
def fibonacci_non_computable_3 (n: Nat) (result: Nat) : Prop :=
  result = fib n

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
def fib_helper : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => 
    let (a, b) := fib_helper n
    (b, a + b)

def implementation (n: Nat) : Nat := (fib_helper n).1

-- LLM HELPER
lemma fib_helper_correct (n: Nat) : (fib_helper n).1 = fib n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [fib_helper]
    let (a, b) := fib_helper n
    simp only [Prod.fst]
    have h : (fib_helper n).1 = a := by simp [a]
    rw [←h, ih]
    cases n with
    | zero => simp [fib]
    | succ m => simp [fib]

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, fibonacci_non_computable_3, implementation]
  exact fib_helper_correct n