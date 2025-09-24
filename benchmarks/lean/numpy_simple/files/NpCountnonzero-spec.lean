-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nonzero {n : Nat} (arr : Vector Float n) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nonzero_spec {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  (num ≥ 0) ∧
  (n > 0 → arr[0]! = 0.0 → nonzero (arr.tail) = num - 1) :=
sorry
-- </vc-theorems>