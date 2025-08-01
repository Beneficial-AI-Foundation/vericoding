import benchmarks.MatrixDef

namespace NpFlatten

def flatten2 {m n : Nat} (mat : Matrix m n Int) : Vector Int (m * n) := sorry

theorem flatten2_spec {m n : Nat} (mat : Matrix m n Int)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  (ret.toList.length = m * n) ∧
  (∀ i j : Nat, i < m → j < n → ret[i * n + j]! = mat[i]![j]!) := sorry

end NpFlatten
