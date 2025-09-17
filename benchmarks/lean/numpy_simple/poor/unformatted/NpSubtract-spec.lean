
def subtract {n : Nat} (a b : Vector Int n) : Vector Int n := sorry

theorem subtract_spec {n : Nat} (a b : Vector Int n) :
  (subtract a b).toList.length = n ∧
  ∀ i : Fin n, (subtract a b)[i] = a[i] - b[i] := sorry
