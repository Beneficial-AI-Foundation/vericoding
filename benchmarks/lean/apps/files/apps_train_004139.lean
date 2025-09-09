-- <vc-helpers>
-- </vc-helpers>

def archers_ready (archers : List Int) : Bool := sorry

theorem empty_list_false : 
  ∀ (archers : List Int), archers = [] → archers_ready archers = false := sorry

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

/-
info: False
-/
-- #guard_msgs in
-- #eval archers_ready []

/-
info: True
-/
-- #guard_msgs in
-- #eval archers_ready [5, 6, 7, 8]

/-
info: False
-/
-- #guard_msgs in
-- #eval archers_ready [1, 2, 3, 4, 5, 6, 7, 8]

-- Apps difficulty: introductory
-- Assurance level: unguarded