-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_place_flowers (flowerbed : List Nat) (n : Nat) : Bool := sorry

theorem flowerbed_returns_bool (flowerbed : List Nat) :
  (∀ x ∈ flowerbed, x = 0 ∨ x = 1) →
  ∃ b : Bool, can_place_flowers flowerbed 0 = b
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maximum_flowers_boundary (flowerbed : List Nat) :
  (∀ x ∈ flowerbed, x = 0 ∨ x = 1) →
  let total_ones := (flowerbed.filter (· = 1)).length
  let n := flowerbed.length + 1 - total_ones
  can_place_flowers flowerbed n = false
  := sorry

theorem all_zeros_array (flowerbed : List Nat) :
  (∀ x ∈ flowerbed, x = 0) →
  flowerbed.length > 0 →
  let max_flowers := (flowerbed.length + 1) / 2
  can_place_flowers flowerbed max_flowers = true
  := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_place_flowers [1, 0, 0, 0, 1] 1

/-
info: False
-/
-- #guard_msgs in
-- #eval can_place_flowers [1, 0, 0, 0, 1] 2

/-
info: True
-/
-- #guard_msgs in
-- #eval can_place_flowers [0, 0, 1, 0, 0] 1
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded