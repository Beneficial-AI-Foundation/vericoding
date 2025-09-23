-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def less {n : Nat} (a b : Vector Int n) : Vector Bool n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem less_spec {n : Nat} (a b : Vector Int n) :
  (less a b).toList.length = n ∧
  ∀ i : Fin n, (less a b)[i] = (a[i] < b[i]) :=
sorry
-- </vc-theorems>