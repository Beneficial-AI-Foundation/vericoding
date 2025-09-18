-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stones_game (n : Nat) (stones : List Nat) : String := sorry

theorem stones_game_output_valid (n : Nat) (stones : List Nat) :
  stones_game n stones = "YES" ∨ stones_game n stones = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stones_game_consistent (stones : List Nat) :
  let n := stones.length
  stones_game n stones = stones_game n stones := sorry
-- </vc-theorems>