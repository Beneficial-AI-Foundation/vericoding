-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def grid_index (grid : List (List Char)) (indexes : List Nat) : List Char := sorry

theorem grid_index_length 
  (grid : List (List Char)) 
  (size : Nat) 
  (chars : List Char)
  (indexes : List Nat)
  (h1 : size > 0)
  (h2 : grid.length = size)
  (h3 : ∀ row ∈ grid, row.length = size)
  (h4 : indexes.all (λ i => i > 0 ∧ i ≤ size * size)) :
  (grid_index grid indexes).length = indexes.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem grid_index_matches_position
  (grid : List (List Char))
  (size : Nat)
  (chars : List Char) 
  (indexes : List Nat)
  (i : Nat)
  (h1 : size > 0)
  (h2 : grid.length = size)
  (h3 : ∀ row ∈ grid, row.length = size)
  (h4 : i < indexes.length)
  (h5 : indexes[i]! > 0 ∧ indexes[i]! ≤ size * size) :
  (grid_index grid indexes)[i]! = grid[(indexes[i]! - 1) / size]![(indexes[i]! - 1) % size]! := sorry

theorem grid_index_uniform_grid
  (size : Nat)
  (c : Char)
  (indexes : List Nat)
  (grid : List (List Char))
  (h1 : size > 0)
  (h2 : grid = List.replicate size (List.replicate size c))
  (h3 : indexes.all (λ i => i > 0 ∧ i ≤ size * size)) :
  (grid_index grid indexes).all (· = c) := sorry

/-
info: 'meal'
-/
-- #guard_msgs in
-- #eval grid_index [["m", "y", "e"], ["x", "a", "m"], ["p", "l", "e"]] [1, 3, 5, 8]

/-
info: 'hello'
-/
-- #guard_msgs in
-- #eval grid_index [["h", "e", "l"], ["l", "o", "!"], ["?", "?", "?"]] [1, 2, 3, 4, 5]

/-
info: 'ad'
-/
-- #guard_msgs in
-- #eval grid_index [["a", "b"], ["c", "d"]] [1, 4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded