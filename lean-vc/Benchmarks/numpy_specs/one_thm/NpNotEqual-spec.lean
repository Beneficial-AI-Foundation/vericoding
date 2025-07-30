namespace NpNotEqual

def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := sorry

theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) := sorry

end NpNotEqual 