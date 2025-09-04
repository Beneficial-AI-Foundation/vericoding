namespace NpLess

def less {n : Nat} (a b : Vector Int n) : Vector Bool n := sorry

theorem less_spec {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n ∧
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) := sorry

end NpLess 