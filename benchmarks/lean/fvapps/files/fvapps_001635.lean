-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dbl_linear (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dbl_linear_positive (n : Nat) : 
  dbl_linear n > 0 := sorry

theorem dbl_linear_strictly_increasing {n₁ n₂ : Nat} (h : n₁ < n₂) : 
  dbl_linear n₁ < dbl_linear n₂ := sorry

theorem dbl_linear_base_case : 
  dbl_linear 0 = 1 := sorry

theorem dbl_linear_sequence_rule {n : Nat} (h : dbl_linear n > 1) :
  ∃ i < n, dbl_linear n = 2 * dbl_linear i + 1 ∨ dbl_linear n = 3 * dbl_linear i + 1 := sorry
-- </vc-theorems>