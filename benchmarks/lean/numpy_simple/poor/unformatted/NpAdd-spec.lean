

def add {n : Nat} (a b : Vector Int n) : Vector Int n := sorry

theorem add_spec {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n ∧
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] := sorry
