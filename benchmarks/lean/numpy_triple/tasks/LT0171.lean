-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diag {n : Nat} (matrix : Vector Float (n * n)) : Vector Float n :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diag_spec {n : Nat} (matrix : Vector Float (n * n)) : 
    ∀ i : Fin n, (diag matrix).get i = matrix.get ⟨i.val * n + i.val, by sorry⟩ := by
  sorry
-- </vc-theorems>