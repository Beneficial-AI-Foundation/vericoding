/-
# NumPy Intersect Specification

Port of np_intersect.dfy to Lean 4
-/

namespace DafnySpecs.NpIntersect

/-- Find intersection of two vectors -/
def intersect {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Vector Float (min n m) := sorry

/-- Specification: Result length is bounded -/
theorem intersect_length_bound {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  ret.toList.length < n ∧ ret.toList.length < m := sorry

/-- Specification: Intersection property -/
theorem intersect_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  ∀ i j : Nat, i < n → j < m →
    (a[i]! = b[j]! → ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) ∧
    (a[i]! ≠ b[j]! → ¬ ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) := sorry

end DafnySpecs.NpIntersect
