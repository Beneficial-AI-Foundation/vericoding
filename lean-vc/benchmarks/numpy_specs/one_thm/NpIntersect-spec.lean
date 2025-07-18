namespace NpIntersect

def intersect {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Vector Float (min n m) := sorry

theorem intersect_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
  let ret := intersect a b
  (ret.toList.length < n ∧ ret.toList.length < m) ∧
  (∀ i j : Nat, i < n → j < m →
    (a[i]! = b[j]! → ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!) ∧
    (a[i]! ≠ b[j]! → ¬ ∃ k : Nat, k < ret.toList.length ∧ ret[k]! = a[i]!)) := sorry

end NpIntersect
