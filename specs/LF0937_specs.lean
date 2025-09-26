-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findRightmostHill (n : Nat) (u : Nat) (d : Nat) (h : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds {n u d : Nat} {h : List Nat} (h_nonempty : h ≠ []) :
  let result := findRightmostHill n u d h
  1 ≤ result ∧ result ≤ h.length :=
sorry

theorem flat_terrain_full_traverse {n u d : Nat} {h : List Nat} 
  (h_len : h.length > 1)
  (h_flat : ∀ (i : Fin (h.length - 1)), h[i] = h[i.val + 1]) :
  findRightmostHill n u d h = h.length :=
sorry

theorem impossible_first_step {n u d : Nat} {h : List Nat}
  (h_len : h.length > 1)
  (h_first_impossible : ∃ (i₁ i₀ : Fin h.length), 
    h[i₁] - h[i₀] > u ∧ h[i₀] - h[i₁] > d) :
  findRightmostHill n u d h = 1 :=
sorry

theorem single_element_result {n u d : Nat} :
  findRightmostHill n u d [n] = 1 :=
sorry
-- </vc-theorems>