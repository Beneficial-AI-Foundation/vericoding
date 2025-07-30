namespace NpMax

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := sorry

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := sorry

end NpMax 