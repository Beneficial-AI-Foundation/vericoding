/-
# NumPy Copy Specification

Port of np_copy.dfy to Lean 4
-/

namespace DafnySpecs.NpCopy

/-- Return an array copy of the given object -/
def copy {n : Nat} (arr : Vector Int n) : Vector Int n := arr

/-- Specification: The result has the same length as input -/
theorem copy_length {n : Nat} (arr : Vector Int n) :
  (copy arr).toList.length = n := by
  simp [copy]
  exact Vector.toList_length arr

/-- Specification: Each element equals the corresponding input element -/
theorem copy_spec {n : Nat} (arr : Vector Int n) :
  ∀ i : Fin n, (copy arr)[i] = arr[i] := by
  intro i
  rfl

end DafnySpecs.NpCopy