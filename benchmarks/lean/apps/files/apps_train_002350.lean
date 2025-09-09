-- <vc-helpers>
-- </vc-helpers>

def divisorGame (n : Nat) : Bool := sorry

theorem divisorGame_type (n : Nat) :
  divisorGame n = true ∨ divisorGame n = false := sorry

theorem divisorGame_parity (n : Nat) :
  divisorGame n = (n % 2 = 0) := sorry

theorem divisorGame_base_cases : 
  divisorGame 1 = false ∧ divisorGame 2 = true := sorry

theorem divisorGame_bounds (n : Nat) : 
  n = 1 ∨ n = 1000 → (divisorGame n = true ∨ divisorGame n = false) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval divisorGame 2

/-
info: False
-/
-- #guard_msgs in
-- #eval divisorGame 3

/-
info: True
-/
-- #guard_msgs in
-- #eval divisorGame 4

-- Apps difficulty: introductory
-- Assurance level: unguarded