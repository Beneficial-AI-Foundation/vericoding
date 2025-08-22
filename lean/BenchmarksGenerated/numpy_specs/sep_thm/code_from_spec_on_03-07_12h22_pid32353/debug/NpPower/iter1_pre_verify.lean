/-
# NumPy Power Specification

Port of np_power.dfy to Lean 4
-/

namespace DafnySpecs.NpPower

/-- Element-wise power of a vector of integers to a vector of natural numbers -/
def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] ^ b[i])

/-- Specification: The result has the same length as inputs -/
theorem power_length {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n := by
  simp [power]
  rw [Vector.toList_ofFn]
  simp [List.length_map]

/-- Specification: Each element is the power of corresponding input elements -/
theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) := by
  intro i
  simp [power]
  rw [Vector.get_ofFn]

end DafnySpecs.NpPower