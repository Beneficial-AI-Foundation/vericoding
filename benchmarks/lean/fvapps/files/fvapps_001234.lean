-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Recipe := (Nat × Nat × Nat)
def calculateLoss (recipes : List Recipe) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem loss_is_nonnegative (recipes : List Recipe) :
  calculateLoss recipes ≥ 0 :=
  sorry

theorem loss_is_zero_no_discount (recipes : List Recipe) :
  (∀ r ∈ recipes, r.2.2 = 0) →
  calculateLoss recipes = 0 :=
  sorry

theorem loss_scales_with_quantity (recipes : List Recipe) :
  let doubled := recipes.map (fun r => (r.1, r.2.1 * 2, r.2.2))
  calculateLoss doubled = 2 * calculateLoss recipes :=
  sorry

theorem max_loss_at_full_discount (recipes : List Recipe) :
  (∀ r ∈ recipes, r.2.2 = 100) →
  calculateLoss recipes = recipes.foldr (fun r acc => r.1 * r.2.1 + acc) 0 :=
  sorry
-- </vc-theorems>