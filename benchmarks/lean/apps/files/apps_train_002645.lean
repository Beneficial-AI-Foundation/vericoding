-- <vc-helpers>
-- </vc-helpers>

def faro_cycles (n : Nat) : Nat := sorry

/- Minimum number of cards (2) requires only one faro cycle -/

theorem faro_cycles_min : faro_cycles 2 = 1 := sorry

/- Faro cycles for even number of cards is always positive -/

theorem faro_cycles_positive_small (n : Nat) : 
  n = 4 ∨ n = 8 → faro_cycles n > 0 := sorry

/- Standard deck of 52 cards requires exactly 8 faro cycles -/

theorem faro_cycles_standard_deck : faro_cycles 52 = 8 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval faro_cycles 2

/-
info: 8
-/
-- #guard_msgs in
-- #eval faro_cycles 52

/-
info: 540
-/
-- #guard_msgs in
-- #eval faro_cycles 542

-- Apps difficulty: introductory
-- Assurance level: guarded