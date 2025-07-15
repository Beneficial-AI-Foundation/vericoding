import benchmarks.MatrixDef

namespace NpTril

def tril {m n : Nat} (arr : Matrix m n Int) (k : Int) : Matrix m n Int := sorry

theorem tril_spec {m n : Nat} (arr : Matrix m n Int) (k : Int)
  (h : -m + 1 < k ∧ k < n - 1) :
  let ret := tril arr k
  (ret.toList.length = m * n) ∧
  (∀ i j : Nat, i < m → j < n →
    if j - i > k then ret[i]![j]! = 0 else ret[i]![j]! = arr[i]![j]!) := sorry

end NpTril
