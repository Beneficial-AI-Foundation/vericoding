-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stoneGameIII (stones: List Int) : String := sorry

theorem stone_game_result_valid (stones : List Int) (h: stones.length ≥ 1) : 
  let result := stoneGameIII stones
  result = "Alice" ∨ result = "Bob" ∨ result = "Tie"
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stone_game_scale_invariant (stones : List Int) (scale : Int) 
  (h1: stones.length ≥ 1) (h2: scale > 0) :
  stoneGameIII stones = stoneGameIII (stones.map (· * scale))
  := sorry
-- </vc-theorems>