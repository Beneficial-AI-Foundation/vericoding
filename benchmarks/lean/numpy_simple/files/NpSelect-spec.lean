-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def select {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) : Vector Float n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem select_spec {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (h1 : m > 0 ∧ n > 0)
  (h2 : ∀ i : Fin m, condlist[i].toList.length = n ∧ choicelist[i].toList.length = n) :
  let ret := select condlist choicelist
  (ret.toList.length = n) ∧
  (∀ i : Fin m, ∀ j : Fin n, condlist[i][j] → ret[j] = choicelist[i][j]) :=
sorry
-- </vc-theorems>