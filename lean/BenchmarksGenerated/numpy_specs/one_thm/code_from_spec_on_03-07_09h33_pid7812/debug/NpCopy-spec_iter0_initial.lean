namespace NpCopy

def copy {n : Nat} (arr : Vector Int n) : Vector Int n := arr

theorem copy_spec {n : Nat} (arr : Vector Int n) :
  (copy arr).toList.length = n ∧
  ∀ i : Fin n, (copy arr)[i] = arr[i] := by
  constructor
  · simp [copy]
    exact Vector.toList_length arr
  · intro i
    simp [copy]

end NpCopy