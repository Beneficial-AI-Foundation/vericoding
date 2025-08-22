namespace NpTranspose

def transpose {m n : Nat} (arr : Matrix Int m n) : Matrix Int n m := 
  Matrix.of (fun i j => arr[j]![i]!)

theorem transpose_spec {m n : Nat} (arr : Matrix Int m n) :
  let ret := transpose arr
  (ret.toList.length = n * m) ∧
  (∀ i j : Nat, i < m → j < n → ret[j]![i]! = arr[i]![j]!) := by
  constructor
  · simp [transpose]
    rw [Matrix.toList_length]
  · intros i j hi hj
    simp [transpose]
    rw [Matrix.of_apply]

end NpTranspose