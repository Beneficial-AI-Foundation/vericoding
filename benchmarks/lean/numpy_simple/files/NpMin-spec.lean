-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] :=
sorry
-- </vc-theorems>