/-
# NumPy Ravel Specification

Port of np_ravel.dfy to Lean 4
-/

namespace DafnySpecs.NpRavel

/-- Flatten array into 1D -/
def ravel {n : Nat} (a : Vector Int n) : Vector Int n := sorry

/-- Specification: The result has same length as input -/
theorem ravel_length {n : Nat} (a : Vector Int n) :
  let ret := ravel a
  ret.toList.length = n := sorry

/-- Specification: Elements are preserved -/
theorem ravel_spec {n : Nat} (a : Vector Int n) :
  let ret := ravel a
  ∀ i : Fin n, ret[i] = a[i] := sorry

end DafnySpecs.NpRavel
