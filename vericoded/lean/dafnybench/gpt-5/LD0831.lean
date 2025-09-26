import Mathlib
-- <vc-preamble>
def Fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => Fibonacci (n + 1) + Fibonacci n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def fibPair : Nat → Nat × Nat
| 0 => (0, 1)
| n + 1 =>
    let p := fibPair n
    (p.2, p.1 + p.2)

-- LLM HELPER
lemma fibPair_spec (n : Nat) :
  fibPair n = (Fibonacci n, Fibonacci (n + 1)) := by
  induction n with
  | zero =>
      simp [fibPair, Fibonacci]
  | succ n ih =>
      calc
        fibPair (n + 1)
            = (Fibonacci (n + 1), Fibonacci n + Fibonacci (n + 1)) := by
                simpa [fibPair, ih, Nat.add_comm]
        _   = (Fibonacci (n + 1), Fibonacci (n + 2)) := by
                have : Fibonacci n + Fibonacci (n + 1) = Fibonacci (n + 2) := by
                  simpa [Fibonacci, Nat.add_comm]
                simpa [this]

-- </vc-helpers>

-- <vc-definitions>
def FibonacciIterative (n : Nat) : Nat :=
(fibPair n).1
-- </vc-definitions>

-- <vc-theorems>
theorem fibonacci_iterative_spec (n : Nat) :
FibonacciIterative n = Fibonacci n :=
by
  simpa [FibonacciIterative, fibPair_spec]
-- </vc-theorems>
