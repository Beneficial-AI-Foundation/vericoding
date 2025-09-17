
def remainder {n : Nat} (a b : Vector Int n) : Vector Int n := sorry

theorem remainder_spec {n : Nat} (a b : Vector Int n)
  (h : ∀ i : Fin n, b[i] ≠ 0) :
  let ret := remainder a b
  (ret.toList.length = n) ∧
  (∀ i : Fin n, ret[i] = a[i] % b[i]) := sorry
