import benchmarks.MatrixDef

namespace NpDiagonal

def diagonal {n : Nat} (arr : Matrix n n Int) (k : Int) : Vector Int (if k > 0 then n - k.natAbs else n + k.natAbs) := sorry

theorem diagonal_spec {n : Nat} (arr : Matrix n n Int) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  (if k > 0 then ret.toList.length = n - k.natAbs else ret.toList.length = n + k.natAbs) ∧
  (∀ i : Nat, i < ret.toList.length →
    if k ≥ 0 then ret[i]! = arr[i]![i + k.natAbs]!
    else ret[i]! = arr[i + k.natAbs]![i]!) := sorry

end NpDiagonal
