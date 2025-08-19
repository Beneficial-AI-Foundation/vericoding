namespace NpCumProd

def cumProd {n : Nat} (a : Vector Int n) : Vector Int n := sorry

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (cumProd a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[i.val - 1]'(by omega) * a[i] := sorry

end NpCumProd 