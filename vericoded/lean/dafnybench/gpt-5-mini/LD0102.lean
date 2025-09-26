import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper definitions required for this simple equivalence.
-- LLM HELPER

-- </vc-helpers>

-- <vc-definitions>
def fib (n : Nat) : Nat :=
match n with
| 0 => 0
| Nat.succ 0 => 1
| Nat.succ (Nat.succ k) => fib (Nat.succ k) + fib k


def fibonacci1 (n : Nat) : Nat :=
fib n

-- </vc-definitions>

-- <vc-theorems>
theorem fibonacci1_spec (n : Nat) :
fibonacci1 n = fib n :=
rfl

-- </vc-theorems>
