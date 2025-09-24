-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def equal {n : Nat} (a b : Vector Int n) : Vector Bool n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_spec {n : Nat} (a b : Vector Int n) :
  (equal a b).toList.length = n ∧
  ∀ i : Fin n, (equal a b)[i] = (a[i] = b[i]) :=
sorry
-- </vc-theorems>