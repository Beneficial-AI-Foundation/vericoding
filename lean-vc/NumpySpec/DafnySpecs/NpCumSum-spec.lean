namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := sorry

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := sorry

end NpCumSum 