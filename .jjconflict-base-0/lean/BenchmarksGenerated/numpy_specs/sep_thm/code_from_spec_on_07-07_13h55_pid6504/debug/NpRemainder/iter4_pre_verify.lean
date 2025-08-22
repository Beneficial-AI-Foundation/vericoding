/-
# NumPy Remainder Specification

Port of np_remainder.dfy to Lean 4
-/

namespace DafnySpecs.NpRemainder

/-- Compute element-wise remainder -/
def remainder {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => a[i] % b[i])

/-- Specification: The result has same length as inputs -/
theorem remainder_length {n : Nat} (a b : Vector Int n)
  (h : ∀ i : Fin n, b[i] ≠ 0) :
  let ret := remainder a b
  ret.toList.length = n := by
  simp [remainder]

/-- Specification: Remainder computation -/
theorem remainder_spec {n : Nat} (a b : Vector Int n)
  (h : ∀ i : Fin n, b[i] ≠ 0) :
  let ret := remainder a b
  ∀ i : Fin n, ret[i] = a[i] % b[i] := by
  intro i
  simp [remainder]

end DafnySpecs.NpRemainder