import Benchmarks.MatrixDef

namespace NpRavel

def ravel {m n : Nat} (arr : Matrix m n Int) : Vector Int (m * n) := sorry

theorem ravel_spec {m n : Nat} (arr : Matrix m n Int) :
  let ret := ravel arr
  (ret.toList.length = m * n) ∧
  (∀ i j : Nat, i < m → j < n → ret[i * n + j]! = arr[i]![j]!) := sorry

end NpRavel
