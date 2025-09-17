
def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n := sorry

theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) := sorry
