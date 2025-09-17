
def bitwiseOr {n : Nat} (a b : Vector Nat n) : Vector Nat n := sorry

theorem bitwiseOr_spec {n : Nat} (a b : Vector Nat n) :
  (bitwiseOr a b).toList.length = n ∧
  ∀ i : Fin n, (bitwiseOr a b)[i] = a[i] ||| b[i] := sorry
