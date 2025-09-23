-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greater {n : Nat} (a b : Vector Int n) : Vector Bool n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greater_spec {n : Nat} (a b : Vector Int n) :
  (greater a b).toList.length = n ∧
  ∀ i : Fin n, (greater a b)[i] = (a[i] > b[i]) :=
sorry
-- </vc-theorems>