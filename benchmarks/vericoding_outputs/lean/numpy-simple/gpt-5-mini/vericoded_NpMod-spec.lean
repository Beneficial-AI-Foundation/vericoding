import Mathlib
-- <vc-preamble>
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- LLM HELPER: small notes and future helpers for Vector utilities
-- We rely on Vector.ofFn and the existing Vector API from Mathlib.
-- If additional lemmas are needed later, add them here.

-- </vc-helpers>

-- <vc-definitions>
def mod {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n :=
Vector.ofFn fun i => a[i] % (b.val[i])
-- </vc-definitions>

-- <vc-theorems>
theorem mod_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (mod a b).toList.length = n ∧
  ∀ i : Fin n, (mod a b)[i] = a[i] % (b.val[i]) :=
by
  constructor
  · simp [mod]
  · intro i; simp [mod]

-- </vc-theorems>
