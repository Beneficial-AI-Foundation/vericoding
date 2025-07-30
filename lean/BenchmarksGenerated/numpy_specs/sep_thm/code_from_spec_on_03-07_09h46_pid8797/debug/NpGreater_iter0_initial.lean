/-
# NumPy Greater Specification

Port of np_greater.dfy to Lean 4
-/

namespace DafnySpecs.NpGreater

/-- Element-wise greater-than comparison of two vectors -/
def greater {n : Nat} (a b : Vector Int n) : Vector Bool n := 
  Vector.ofFn (fun i => a[i] > b[i])

/-- Specification: The result has the same length as inputs -/
theorem greater_length {n : Nat} (a b : Vector Int n) :
  (greater a b).toList.length = n := by
  simp [greater]
  rw [Vector.toList_ofFn]
  simp

/-- Specification: Each element is true iff first input element is greater than second -/
theorem greater_spec {n : Nat} (a b : Vector Int n) :
  ∀ i : Fin n, (greater a b)[i] = (a[i] > b[i]) := by
  intro i
  simp [greater]
  rw [Vector.get_ofFn]

end DafnySpecs.NpGreater