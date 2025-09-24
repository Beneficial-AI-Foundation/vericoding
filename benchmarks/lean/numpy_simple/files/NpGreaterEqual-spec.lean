-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greaterEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greaterEqual_spec {n : Nat} (a b : Vector Int n) :
  (greaterEqual a b).toList.length = n ∧
  ∀ i : Fin n, (greaterEqual a b)[i] = (a[i] ≥ b[i]) :=
sorry
-- </vc-theorems>