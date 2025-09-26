import Mathlib
-- <vc-preamble>
def Fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => Fibonacci (n + 1) + Fibonacci n
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
private def fibonacciIterative_aux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibonacciIterative_aux n b (a + b)

-- LLM HELPER
private theorem fib_add (n : Nat) : Fibonacci (n + 2) = Fibonacci (n + 1) + Fibonacci n := by
  rfl

-- LLM HELPER
private theorem fibonacciIterative_aux_spec (k : Nat) : ∀ i,
  fibonacciIterative_aux k (Fibonacci i) (Fibonacci (i + 1)) = Fibonacci (i + k) := by
  induction k with
  | zero =>
    intro i
    simp [fibonacciIterative_aux]
  | succ k' ih =>
    intro i
    rw [fibonacciIterative_aux]
    rw [add_comm (Fibonacci i) (Fibonacci (i+1))]
    rw [← fib_add i]
    rw [ih (i + 1)]
    rw [Nat.add_assoc, Nat.add_comm 1]

-- </vc-helpers>

-- <vc-definitions>
def FibonacciIterative (n : Nat) : Nat :=
(fibonacciIterative_aux n 0 1)
-- </vc-definitions>

-- <vc-theorems>
theorem fibonacci_iterative_spec (n : Nat) :
FibonacciIterative n = Fibonacci n :=
by
  rw [FibonacciIterative]
  have h := fibonacciIterative_aux_spec n 0
  simp [Fibonacci] at h
  exact h
-- </vc-theorems>
