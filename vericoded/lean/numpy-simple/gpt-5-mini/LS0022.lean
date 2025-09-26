import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- LLM HELPER
-- Helper definitions/notes for the elementwise `greater` implementation.
-- We implement `greater` elementwise using `Vector.ofFn` and rely on the
-- standard `Vector` operations from Mathlib/Std. No additional declarations
-- are required for the correctness proof below.
-- </vc-helpers>

-- <vc-definitions>
def greater {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn fun i => a[i] > b[i]
-- </vc-definitions>

-- <vc-theorems>
theorem greater_spec {n : Nat} (a b : Vector Int n) :
  (greater a b).toList.length = n ∧
  ∀ i : Fin n, (greater a b)[i] = (a[i] > b[i]) :=
by
  dsimp [greater]
  constructor
  · simp
  · intro i
    simp
-- </vc-theorems>
