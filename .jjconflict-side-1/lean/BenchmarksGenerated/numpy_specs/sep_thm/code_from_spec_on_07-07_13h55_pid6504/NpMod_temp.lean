/-
# NumPy Mod Specification

Port of np_mod.dfy to Lean 4
-/

namespace DafnySpecs.NpMod

/-- Type constraint ensuring all elements are non-zero -/
def NonZeroVector (n : Nat) := { v : Vector Int n // ∀ i : Fin n, v[i] ≠ 0 }

/-- Element-wise modulo of two vectors -/
def mod {n : Nat} (a : Vector Int n) (b : NonZeroVector n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] % b.val[i])

/-- Specification: The result has the same length as inputs -/
theorem mod_length {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  (mod a b).toList.length = n := by
  simp [mod, Vector.toList_ofFn, List.length_ofFn]

/-- Specification: Each element is the modulo of corresponding input elements -/
theorem mod_spec {n : Nat} (a : Vector Int n) (b : NonZeroVector n) :
  ∀ i : Fin n, (mod a b)[i] = a[i] % (b.val[i]) := by
  intro i
  simp [mod]

end DafnySpecs.NpMod