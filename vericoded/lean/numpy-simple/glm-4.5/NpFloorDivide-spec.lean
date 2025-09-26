import Mathlib
-- <vc-preamble>
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def Vector.ofFn_helper {α n} (f : Fin n → α) : Vector α n :=
  Vector.ofFn f

-- LLM HELPER
theorem Vector.ofFn_length {α n} (f : Fin n → α) : (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn]

-- LLM HELPER
theorem Vector.ofFn_get {α n} (f : Fin n → α) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]
-- </vc-helpers>

-- <vc-definitions>
def floorDivide {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n :=
Vector.ofFn fun i : Fin n => a[i] / (b.val[i])
-- </vc-definitions>

-- <vc-theorems>
theorem floorDivide_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (floorDivide a b).toList.length = n ∧
  ∀ i : Fin n, (floorDivide a b)[i] = a[i] / (b.val[i]) :=
⟨
  by rw [floorDivide]; apply Vector.ofFn_length,
  fun i => by rw [floorDivide]; apply Vector.ofFn_get
⟩
-- </vc-theorems>
