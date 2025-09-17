
def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n := sorry

theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n ∧
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] := sorry
