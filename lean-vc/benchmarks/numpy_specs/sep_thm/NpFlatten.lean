/-
# NumPy Flatten Specification

Port of np_flatten.dfy to Lean 4
-/

namespace DafnySpecs.NpFlatten

/-- Flatten a 2D matrix to a 1D vector -/
def flatten2 {m n : Nat} (mat : Matrix Int m n) : Vector Int (m * n) := sorry

/-- Specification: The result has correct length -/
theorem flatten2_length {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ret.toList.length = m * n := sorry

/-- Specification: Elements are correctly indexed -/
theorem flatten2_spec {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ∀ i j : Nat, i < m → j < n → ret[i * n + j]! = mat[i]![j]! := sorry

end DafnySpecs.NpFlatten
