-- <vc-preamble>
def Fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => Fibonacci (n + 1) + Fibonacci n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FibonacciIterative (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fibonacci_iterative_spec (n : Nat) :
FibonacciIterative n = Fibonacci n :=
sorry
-- </vc-theorems>