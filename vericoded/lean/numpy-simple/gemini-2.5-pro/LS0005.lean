import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- This file defines a bitwise AND operation on vectors of natural numbers and proves its properties.
-- No additional helper functions or imports are required beyond `import Mathlib`,
-- as it provides `Vector` from `Std` and the necessary tactics and lemmas.
-- </vc-helpers>

-- <vc-definitions>
def bitwiseAnd {n : Nat} (a b : Vector Nat n) : Vector Nat n :=
Vector.zipWith (· &&& ·) a b
-- </vc-definitions>

-- <vc-theorems>
theorem bitwiseAnd_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseAnd a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseAnd a b)[i] = a[i] &&& b[i] :=
by
  -- Unfold the definition to work with the underlying `Vector.zipWith` function.
  unfold bitwiseAnd
  -- We need to prove a conjunction, so we use `constructor` to split the goal into two.
  constructor
  -- Goal 1: The length of the resulting vector's list is `n`.
  · -- This is true by definition for any `Vector α n`.
    -- The `simp` tactic can prove this using `Vector.toList_length` and `Vector.length_zipWith`.
    simp
  -- Goal 2: Each element `i` of the result is the bitwise AND of the corresponding elements of the inputs.
  · -- Introduce an arbitrary index `i`.
    intro i
    -- This follows directly from the definition of `Vector.zipWith`.
    -- The `simp` tactic can prove this using the `Vector.get_zipWith` lemma.
    simp
-- </vc-theorems>
