import Benchmarks.MatrixDef

namespace NpBroadcast

def broadcast {n m k : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix m k Int := sorry

theorem broadcast_spec {n m k : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h1 : shape[0]'sorry = m) (h2 : shape[1]'sorry = k) (h3 : m = n ∨ k = n) :
  let ret := @broadcast n m k a shape
  (ret.toList.length = m * k) ∧
  (∀ i j : Nat, i < m → j < k →
    if m = n then (ret[i]'sorry)[j]'sorry = a[i]'sorry else (ret[i]'sorry)[j]'sorry = a[j]'sorry) := sorry

end NpBroadcast
