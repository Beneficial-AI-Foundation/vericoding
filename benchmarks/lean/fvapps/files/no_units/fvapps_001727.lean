-- <vc-preamble>
def trim : List (List Nat) → List (List Nat) := sorry
def next_gen : List (List Nat) → List (List Nat) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_generation : List (List Nat) → Nat → List (List Nat) := sorry

theorem static_block_pattern :
  next_gen [[1,1], [1,1]] = [[1,1], [1,1]] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_grid_static :
  next_gen [[]] = [[]] := sorry
-- </vc-theorems>