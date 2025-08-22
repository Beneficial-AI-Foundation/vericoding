/-
# NumPy Less Specification

Port of np_less.dfy to Lean 4
-/

namespace DafnySpecs.NpLess

/-- Element-wise less-than comparison of two vectors -/
def less {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] < b[i])

/-- Specification: The result has the same length as inputs -/
theorem less_length {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n := by
  simp [less, Vector.toList_ofFn, List.length_ofFn]

/-- Specification: Each element is true iff first input element is less than second -/
theorem less_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) := by
  intro i
  simp [less, Vector.ofFn_get]

end DafnySpecs.NpLess