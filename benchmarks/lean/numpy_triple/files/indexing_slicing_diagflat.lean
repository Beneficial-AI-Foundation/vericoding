-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagflat {n : Nat} (v : Vector Float n) : Vector (Vector Float n) n :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagflat_spec {n : Nat} (v : Vector Float n) :
    let result := diagflat v
    ∀ i : Fin n, ∀ j : Fin n,
      (i = j → (result.get i).get j = v.get i) ∧
      (i ≠ j → (result.get i).get j = 0) := by
  sorry
-- </vc-theorems>