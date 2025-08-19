namespace NpCopy

def copy {n : Nat} (arr : Vector Int n) : Vector Int n := sorry

theorem copy_spec {n : Nat} (arr : Vector Int n) :
  (copy arr).toList.length = n ∧
  ∀ i : Fin n, (copy arr)[i] = arr[i] := sorry

end NpCopy 