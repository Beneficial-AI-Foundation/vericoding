-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def doubles (k n : Nat) : Float := sorry

theorem doubles_positive_bounded {k n : Nat} (hk : k > 0) (hn : n > 0) : 
  doubles k n > 0 ∧ doubles k n < 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem doubles_increases_with_n {k n₁ n₂ : Nat} (hk : k > 0) (hn : n₁ < n₂) :
  doubles k n₁ < doubles k n₂ := sorry 

theorem doubles_convergence {n : Nat} (hn : n > 0) :
  ∀ i : Nat, i + 1 < n → 
    doubles 1 (i + 2) - doubles 1 (i + 1) < doubles 1 (i + 1) - doubles 1 i := sorry
-- </vc-theorems>