-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gta (base : Nat) (n1 : Nat) (n2 : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gta_positive (base n₁ n₂ : Nat) :
  gta base n₁ n₂ > 0 := by sorry 

theorem gta_natural (base n₁ n₂ : Nat) :
  gta base n₁ n₂ ≥ 0 := by sorry

theorem gta_commutative (base n₁ n₂ : Nat) :
  gta base n₁ n₂ = gta base n₂ n₁ := by sorry

theorem gta_specific_case1 :
  gta 7 123489 5 = 328804 := by sorry

theorem gta_specific_case2 :
  gta 8 12348 47 = 3836040 := by sorry
-- </vc-theorems>