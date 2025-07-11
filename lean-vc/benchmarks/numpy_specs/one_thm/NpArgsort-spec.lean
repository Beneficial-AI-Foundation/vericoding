namespace NpArgsort

def argsort {n : Nat} (a : Vector Float n) : Vector (Fin n) n := sorry

theorem argsort_spec {n : Nat} (a : Vector Float n) :
  (argsort a).toList.length = n ∧
  (∀ i j : Fin n, i < j → a[(argsort a)[i]] ≤ a[(argsort a)[j]]) ∧
  (∀ i : Fin n, ∃ j : Fin n, (argsort a)[j] = i) :=
sorry

end NpArgsort