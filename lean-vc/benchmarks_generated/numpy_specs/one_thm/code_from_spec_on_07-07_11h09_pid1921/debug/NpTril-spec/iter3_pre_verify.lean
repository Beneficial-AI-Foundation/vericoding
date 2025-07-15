namespace NpTril

def tril {m n : Nat} (arr : Matrix Int m n) (k : Int) : Matrix Int m n :=
  Matrix.of fun i j => if (j : Int) - (i : Int) > k then 0 else arr i j

theorem tril_spec {m n : Nat} (arr : Matrix Int m n) (k : Int)
  (h : -m + 1 < k ∧ k < n - 1) :
  let ret := tril arr k
  (ret.toList.length = m * n) ∧
  (∀ i j : Nat, i < m → j < n →
    if (j : Int) - (i : Int) > k then ret i j = 0 else ret i j = arr i j) := by
  simp [tril]
  constructor
  · exact Matrix.toList_length
  · intro i j hi hj
    rfl

end NpTril