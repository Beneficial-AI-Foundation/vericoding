import Mathlib
-- <vc-preamble>
def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Compute Fibonacci using iteration with accumulators
def fibIter : Nat → Nat → Nat → Nat → Nat
  | 0, _, acc1, _ => acc1
  | n + 1, k, acc1, acc2 => fibIter n (k + 1) acc2 (acc1 + acc2)

-- LLM HELPER
lemma fibIter_spec (n k : Nat) (acc1 acc2 : Nat) :
  acc1 = fib k → acc2 = fib (k + 1) → fibIter n k acc1 acc2 = fib (n + k) := by
  induction n generalizing k acc1 acc2 with
  | zero => 
    intros h1 _
    simp [fibIter]
    exact h1
  | succ n ih =>
    intros h1 h2
    simp [fibIter]
    -- Apply IH with shifted parameters
    have := ih (k + 1) acc2 (acc1 + acc2)
    rw [this]
    · -- Prove n + (k + 1) = n + 1 + k
      congr 1
      ring
    · -- acc2 = fib (k + 1) is already h2
      exact h2
    · -- Prove acc1 + acc2 = fib (k + 2)
      rw [h1, h2]
      -- fib k + fib (k + 1) = fib (k + 2) by definition
      show fib k + fib (k + 1) = fib (k + 2)
      -- This follows from the definition of fib
      conv_rhs => unfold fib
      -- For k ≥ 0, fib (k + 2) = fib (k + 1) + fib k
      ring
-- </vc-helpers>

-- <vc-definitions>
def ComputeFib (n : Nat) : Nat :=
fibIter n 0 0 1
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeFib_spec (n : Nat) :
ComputeFib n = fib n :=
by
  unfold ComputeFib
  have h := fibIter_spec n 0 0 1 rfl rfl
  simp at h
  exact h
-- </vc-theorems>
