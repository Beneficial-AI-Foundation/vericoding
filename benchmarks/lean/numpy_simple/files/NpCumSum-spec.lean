-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cumSum {n : Nat} (a : Vector Int n) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cumSum_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  (cumSum a)[0] = a[0] ∧
  ∀ i : Fin n, i.val > 0 →
    let j : Fin n := ⟨i.val - 1, by sorry⟩
    (cumSum a)[i] = (cumSum a)[j] + a[i] :=
sorry
-- </vc-theorems>