-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def archers_ready (archers : List Int) : Bool := sorry

theorem empty_list_false : 
  ∀ (archers : List Int), archers = [] → archers_ready archers = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_above_five_true :
  ∀ (archers : List Int), 
    archers ≠ [] → 
    (∀ x ∈ archers, x ≥ 5) → 
    archers_ready archers = true := sorry

theorem any_below_five_false :
  ∀ (archers : List Int),
    archers ≠ [] →
    (∀ x ∈ archers, x ≤ 4) →
    archers_ready archers = false := sorry

theorem any_below_five_makes_false :
  ∀ (archers : List Int),
    (∃ x ∈ archers, x < 5) →
    archers_ready archers = false := sorry
-- </vc-theorems>