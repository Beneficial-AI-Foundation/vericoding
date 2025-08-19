namespace NpSign

def sign {n : Nat} (a : Vector Int n) : Vector Int n := sorry

theorem sign_spec {n : Nat} (a : Vector Int n) :
  (sign a).toList.length = n ∧
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) := sorry

end NpSign 