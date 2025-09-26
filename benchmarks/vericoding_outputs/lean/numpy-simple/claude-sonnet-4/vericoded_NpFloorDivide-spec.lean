import Mathlib
-- <vc-preamble>
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed - using existing Mathlib lemmas
-- </vc-helpers>

-- <vc-definitions>
def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n :=
Vector.ofFn fun i => a[i] / b.val[i]
-- </vc-definitions>

-- <vc-theorems>
theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n ∧
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) :=
⟨by simp [floorDivide], fun i => by simp [floorDivide]⟩
-- </vc-theorems>
