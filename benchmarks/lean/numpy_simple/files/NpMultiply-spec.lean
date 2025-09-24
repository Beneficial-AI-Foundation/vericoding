-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiply {n : Nat} (a b : Vector Int n) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_spec {n : Nat} (a b : Vector Int n) :
  (multiply a b).toList.length = n ∧
  ∀ i : Fin n, (multiply a b)[i] = a[i] * b[i] :=
sorry
-- </vc-theorems>