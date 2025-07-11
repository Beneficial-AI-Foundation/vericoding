/-
# NumPy Transpose Specification

Port of np_transpose.dfy to Lean 4
-/

namespace DafnySpecs.NpTranspose

/-- Transpose a 2D matrix -/
def transpose {m n : Nat} (a : Matrix Int m n) : Matrix Int n m := sorry

/-- Specification: Transpose preserves dimensions -/
theorem transpose_dimensions {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ret.toList.length = n * m := sorry

/-- Specification: Elements are correctly transposed -/
theorem transpose_spec {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ∀ i j : Nat, i < m → j < n → ret[j]![i]! = a[i]![j]! := sorry

end DafnySpecs.NpTranspose
