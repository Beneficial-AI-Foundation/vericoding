namespace NpUniqueall

def unique_all {n : Nat} (arr : Vector Int n) : Vector Int n := sorry

theorem unique_all_spec {n : Nat} (arr : Vector Int n) :
  let ret := unique_all arr
  (ret.toList.length ≤ n) ∧
  (∀ i : Fin n, ∃ j : Nat, j < ret.toList.length ∧ ret[j]! = arr[i]) ∧
  (∀ i j : Nat, i < ret.toList.length → j < i → ret[i]! ≠ ret[j]!) := sorry

end NpUniqueall
