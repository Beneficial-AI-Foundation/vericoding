import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Compute the pair (fib n, fib (n+1)) iteratively. -/
def fibPair : Nat → Nat × Nat
| 0 => (0, 1)
| Nat.succ n =>
  let p := fibPair n
  (p.2, p.1 + p.2)
-- </vc-helpers>

-- <vc-definitions>
def fib (n : Nat) : Nat :=
(fibPair n).1

def fibonacci1 (n : Nat) : Nat :=
(fibPair n).1
-- </vc-definitions>

-- <vc-theorems>
theorem fibonacci1_spec (n : Nat) :
fibonacci1 n = fib n :=
rfl
-- </vc-theorems>
