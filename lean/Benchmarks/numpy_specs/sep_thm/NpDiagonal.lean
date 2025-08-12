/-
# NumPy Diagonal Specification

Port of np_diagonal.dfy to Lean 4
-/

import Benchmarks.MatrixDef

namespace DafnySpecs.NpDiagonal

/-- Extract diagonal elements from a square matrix -/
def diagonal {n : Nat} (arr : Matrix n n Int) (k : Int) : Vector Int (if k > 0 then n - k.natAbs else n + k.natAbs) := sorry

/-- Specification: The result has correct length -/
theorem diagonal_length {n : Nat} (arr : Matrix n n Int) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  if k > 0 then ret.toList.length = n - k.natAbs else ret.toList.length = n + k.natAbs := sorry

/-- Specification: Elements are correctly extracted -/
theorem diagonal_spec {n : Nat} (arr : Matrix n n Int) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  ∀ i : Nat, i < ret.toList.length →
    if k ≥ 0 then ret[i]! = arr[i]![i + k.natAbs]!
    else ret[i]! = arr[i + k.natAbs]![i]! := sorry

end DafnySpecs.NpDiagonal
