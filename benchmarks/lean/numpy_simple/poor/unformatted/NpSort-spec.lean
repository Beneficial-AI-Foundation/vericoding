
def sort {n : Nat} (a : Vector Float n) : Vector Float n := sorry

theorem sort_spec {n : Nat} (a : Vector Float n) :
  (sort a).toList.length = n ∧
  (∀ i j : Fin n, i < j → (sort a)[i] ≤ (sort a)[j]) ∧
  (∀ x : Float, (sort a).toList.count x = a.toList.count x) :=
sorry
