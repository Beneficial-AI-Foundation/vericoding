namespace NpTranspose

def transpose {m n : Nat} (arr : Matrix Int m n) : Matrix Int n m := sorry

theorem transpose_spec {m n : Nat} (arr : Matrix Int m n) :
  let ret := transpose arr
  (ret.toList.length = n * m) ∧
  (∀ i j : Nat, i < m → j < n → ret[j]![i]! = arr[i]![j]!) := sorry

end NpTranspose
