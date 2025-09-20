-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stones_game (n : Nat) (stones : List Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stones_game_output_valid (n : Nat) (stones : List Nat) :
  stones_game n stones = "YES" ∨ stones_game n stones = "NO" :=
sorry

theorem stones_game_consistent (stones : List Nat) :
  let n := stones.length
  stones_game n stones = stones_game n stones :=
sorry

theorem stones_game_permutation_invariant (stones stones_permuted : List Nat) :
  stones.length = stones_permuted.length →
  stones_game stones.length stones = stones_game stones_permuted.length stones_permuted :=
sorry

theorem stones_game_identical_stones (n : Nat) :
  let stones := List.replicate n 1
  stones_game n stones = stones_game n stones :=
sorry
-- </vc-theorems>