/-
# NumPy Reshape Specification

Port of np_reshape.dfy to Lean 4
-/

import Benchmarks.MatrixDef

namespace DafnySpecs.NpReshape

/-- Reshape vector to new dimensions -/
def reshape {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2) : Matrix m k Int := sorry

/-- Specification: Element count is preserved -/
theorem reshape_count {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ret.toList.length = n := sorry

/-- Specification: Elements are correctly mapped -/
theorem reshape_spec {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ∀ i j : Nat, i < m → j < k → ret[i]![j]! = a[i * k + j]! := sorry

end DafnySpecs.NpReshape
