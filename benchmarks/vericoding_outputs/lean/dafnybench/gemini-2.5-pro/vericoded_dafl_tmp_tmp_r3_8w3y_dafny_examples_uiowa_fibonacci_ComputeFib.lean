import Mathlib
-- <vc-preamble>
def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n
-- </vc-preamble>

-- <vc-helpers>
def fib.loop : Nat → Nat → Nat → Nat
| 0, a, _ => a
| n + 1, a, b => fib.loop n b (a + b)

-- LLM HELPER
theorem fib_add_two (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

-- LLM HELPER
theorem fib_loop_fib (k m : Nat) : fib.loop k (fib m) (fib (m+1)) = fib (m + k) := by
  induction k generalizing m with
  | zero =>
    simp [fib.loop]
  | succ k' ih =>
    simp only [fib.loop]
    rw [add_comm (fib m) (fib (m + 1)), ← fib_add_two m]
    rw [ih (m + 1)]
    apply congrArg fib
    ac_rfl
-- </vc-helpers>

-- <vc-definitions>
def ComputeFib (n : Nat) : Nat :=
fib.loop n 0 1
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeFib_spec (n : Nat) :
ComputeFib n = fib n :=
by
  unfold ComputeFib
  convert fib_loop_fib n 0
  simp [fib]
-- </vc-theorems>
