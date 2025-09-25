-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i]
  ∧
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]
  :=
sorry
-- </vc-theorems>