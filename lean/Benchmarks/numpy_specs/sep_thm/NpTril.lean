/-
# NumPy Tril Specification

Port of np_tril.dfy to Lean 4
-/

import Benchmarks.MatrixDef

namespace DafnySpecs.NpTril

/-- Extract lower triangular part of matrix -/
def tril {m n : Nat} (a : Matrix m n Int) (k : Int) : Matrix m n Int := sorry

/-- Specification: Result has same dimensions -/
theorem tril_dimensions {m n : Nat} (a : Matrix m n Int) (k : Int) :
  let ret := tril a k
  ret.toList.length = m * n := sorry

/-- Specification: Lower triangular elements are preserved -/
theorem tril_spec {m n : Nat} (a : Matrix m n Int) (k : Int) :
  let ret := tril a k
  ∀ i j : Nat, i < m → j < n →
    if j ≤ i + k.natAbs then ret[i]![j]! = a[i]![j]! else ret[i]![j]! = 0 := sorry

end DafnySpecs.NpTril
