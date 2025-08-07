/-
# NumPy Broadcast Specification

Port of np_broadcast.dfy to Lean 4
-/

import benchmarks.MatrixDef

namespace DafnySpecs.NpBroadcast

/-- Broadcast a vector to a 2D shape -/
def broadcast {n m k : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix m k Int := sorry

/-- Specification: The result has the correct dimensions -/
theorem broadcast_length {n m k : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h1 : shape[0]'sorry = m) (h2 : shape[1]'sorry = k) (h3 : m = n ∨ k = n) :
  let ret := @broadcast n m k a shape
  ret.toList.length = m * k := sorry

/-- Specification: Elements are correctly broadcasted -/
theorem broadcast_spec {n m k : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h1 : shape[0]'sorry = m) (h2 : shape[1]'sorry = k) (h3 : m = n ∨ k = n) :
  let ret := @broadcast n m k a shape
  ∀ i j : Nat, i < m → j < k →
    if m = n then (ret[i]'sorry)[j]'sorry = a[i]'sorry else (ret[i]'sorry)[j]'sorry = a[j]'sorry := sorry

end DafnySpecs.NpBroadcast
