-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>