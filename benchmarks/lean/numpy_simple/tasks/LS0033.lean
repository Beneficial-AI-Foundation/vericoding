-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a :=
sorry
-- </vc-theorems>