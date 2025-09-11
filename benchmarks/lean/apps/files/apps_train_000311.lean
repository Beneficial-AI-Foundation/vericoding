-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 'Bob'
-/
-- #guard_msgs in
-- #eval stoneGameIII [1, 2, 3, 7]

/-
info: 'Alice'
-/
-- #guard_msgs in
-- #eval stoneGameIII [1, 2, 3, -9]

/-
info: 'Tie'
-/
-- #guard_msgs in
-- #eval stoneGameIII [1, 2, 3, 6]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded