-- <vc-preamble>
def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ComputeFib (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeFib_spec (n : Nat) :
ComputeFib n = fib n :=
sorry
-- </vc-theorems>