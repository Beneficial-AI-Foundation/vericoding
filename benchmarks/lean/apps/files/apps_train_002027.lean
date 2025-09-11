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

/- We can represent permutation invariance by showing that if we have
    two lists with the same elements (possibly in different order), 
    they produce the same result -/

theorem stones_game_permutation_invariant (stones stones_permuted : List Nat) :
  stones.length = stones_permuted.length →
  stones_game stones.length stones = stones_game stones_permuted.length stones_permuted := sorry

theorem stones_game_identical_stones (n : Nat) :
  let stones := List.replicate n 1
  stones_game n stones = stones_game n stones := sorry

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval stones_game 1 [5]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval stones_game 2 [1, 2]

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval stones_game 3 [34, 44, 21]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded