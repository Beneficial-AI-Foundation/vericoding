-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add {n : Nat} (a b : Vector Int n) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_spec {n : Nat} (a b : Vector Int n) :
  (add a b).toList.length = n ∧
  ∀ i : Fin n, (add a b)[i] = a[i] + b[i] :=
sorry
-- </vc-theorems>