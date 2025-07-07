namespace NpColumnStack

def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix Int m n := sorry

theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  (ret.toList.length = m * n) ∧
  (∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[j]![i]! = input[i]![j]!) := sorry

end NpColumnStack
