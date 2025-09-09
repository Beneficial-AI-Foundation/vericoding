-- <vc-helpers>
-- </vc-helpers>

def diagflat {n : Nat} (v : Vector Float n) : Vector (Vector Float n) n :=
  sorry

theorem diagflat_spec {n : Nat} (v : Vector Float n) :
    let result := diagflat v
    ∀ i : Fin n, ∀ j : Fin n,
      (i = j → (result.get i).get j = v.get i) ∧
      (i ≠ j → (result.get i).get j = 0) := by
  sorry
