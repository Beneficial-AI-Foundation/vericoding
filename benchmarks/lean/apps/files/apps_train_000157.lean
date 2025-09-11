-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stoneGame (piles : List Nat) : Bool := sorry

theorem stone_game_all_evens (piles : List Nat) :
  piles.length ≥ 2 → 
  piles.length % 2 = 0 →
  (∀ x ∈ piles, x > 0) →
  stoneGame piles = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stone_game_realistic_sizes (piles : List Nat) :
  piles.length ≥ 2 →
  piles.length ≤ 100 →
  piles.length % 2 = 0 →
  (∀ x ∈ piles, x > 0) →
  stoneGame piles = true := sorry

theorem stone_game_minimal :
  stoneGame [1, 1] = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval stone_game [5, 3, 4, 5]

/-
info: True
-/
-- #guard_msgs in
-- #eval stone_game [3, 7, 2, 3]

/-
info: True
-/
-- #guard_msgs in
-- #eval stone_game [1, 2, 3, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded