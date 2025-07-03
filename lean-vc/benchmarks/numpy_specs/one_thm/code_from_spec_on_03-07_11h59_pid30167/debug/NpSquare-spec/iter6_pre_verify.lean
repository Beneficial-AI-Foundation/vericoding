namespace NpSquare

def square {n : Nat} (arr : Vector Int n) : Vector Int n := 
  arr.map (fun x => x * x)

theorem square_spec {n : Nat} (arr : Vector Int n) :
  (square arr).toList.length = n ∧
  ∀ i : Fin n, (square arr)[i] = (arr[i]) * (arr[i]) := by
  constructor
  · simp [square, Vector.toList_map]
  · intro i
    simp [square, Vector.get_map]

end NpSquare