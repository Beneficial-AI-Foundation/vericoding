namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := sorry

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := sorry

end NpMin 