-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def champagne_tower (poured : Float) (query_row glass : Nat) : Float := sorry

theorem champagne_tower_bounds
  (poured : Float) (query_row glass : Nat)
  (h1 : poured ≥ 0) :
  let result := champagne_tower poured query_row glass
  0 ≤ result ∧ result ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem champagne_tower_glass_position
  (poured : Float) (query_row glass : Nat)
  (h1 : poured ≥ 0)
  (h2 : glass > query_row) :
  champagne_tower poured query_row glass = 0 := sorry

theorem champagne_tower_zero_poured
  (query_row glass : Nat) :
  champagne_tower 0 query_row glass = 0 := sorry

theorem champagne_tower_first_glass
  (poured : Float)
  (h1 : poured ≥ 0) :
  champagne_tower poured 0 0 = min 1 poured := sorry

theorem champagne_tower_symmetry
  (poured : Float) (row glass : Nat)
  (h1 : poured ≥ 1)
  (h2 : row ≥ 0)
  (h3 : glass ≤ row) :
  champagne_tower poured row glass = champagne_tower poured row (row - glass) := sorry

theorem champagne_tower_filled_glasses_bound_1
  (h1 : poured = 1) :
  (∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → True)) ∧
  (∃ n, n ≤ 1 ∧ ∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → n > 0)) := sorry

theorem champagne_tower_filled_glasses_bound_2
  (h1 : poured = 2) :
  (∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → True)) ∧
  (∃ n, n ≤ 3 ∧ ∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → n > 0)) := sorry

theorem champagne_tower_filled_glasses_bound_4
  (h1 : poured = 4) :
  (∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → True)) ∧
  (∃ n, n ≤ 6 ∧ ∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → n > 0)) := sorry

theorem champagne_tower_filled_glasses_bound_8
  (h1 : poured = 8) :
  (∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → True)) ∧
  (∃ n, n ≤ 10 ∧ ∀ row glass, row < 20 → glass ≤ row →
    (champagne_tower poured row glass > 0 → n > 0)) := sorry

/-
info: 0.0
-/
-- #guard_msgs in
-- #eval champagne_tower 1 1 1

/-
info: 0.5
-/
-- #guard_msgs in
-- #eval champagne_tower 2 1 1

/-
info: 1.0
-/
-- #guard_msgs in
-- #eval champagne_tower 100000009 33 17
-- </vc-theorems>