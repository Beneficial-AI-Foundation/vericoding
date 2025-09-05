namespace NpLessEqual

def lessEqual {n : Nat} (a b : Vector Int n) : Vector Bool n := sorry

theorem lessEqual_spec {n : Nat} (a b : Vector Int n) :
  (lessEqual a b).toList.length = n ∧
  ∀ i : Fin n, (lessEqual a b)[i] = (a[i] ≤ b[i]) := sorry

end NpLessEqual 