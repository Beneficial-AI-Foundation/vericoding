-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def square {n : Nat} (arr : Vector Int n) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_spec {n : Nat} (arr : Vector Int n) :
  (square arr).toList.length = n ∧
  ∀ i : Fin n, (square arr)[i] = (arr[i]) * (arr[i]) :=
sorry
-- </vc-theorems>