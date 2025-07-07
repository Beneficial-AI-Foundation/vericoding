namespace NpCountnonzero

def nonzero {n : Nat} (arr : Vector Float n) : Nat := sorry

theorem nonzero_spec {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  (num ≥ 0) ∧
  (n > 0 → arr[0]! = 0.0 → nonzero (arr.tail) = num - 1) := sorry

end NpCountnonzero
