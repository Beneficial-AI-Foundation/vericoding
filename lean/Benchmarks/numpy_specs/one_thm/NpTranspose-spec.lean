import Benchmarks.MatrixDef

namespace NpTranspose

def transpose {m n : Nat} (arr : Matrix m n Int) : Matrix n m Int := sorry

theorem transpose_spec {m n : Nat} (arr : Matrix m n Int) :
  let ret := transpose arr
  (ret.toList.length = n * m) ∧
  (∀ i j : Nat, i < m → j < n → ret[j]![i]! = arr[i]![j]!) := sorry

end NpTranspose
