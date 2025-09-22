-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_snake_parade (n l a b : Nat) (positions : List Nat) : Nat := sorry

theorem snake_parade_basic_properties
  (n l : Nat)
  (starting_positions : List Nat)
  (h1 : n > 0)
  (h2 : l > 0)
  (h3 : starting_positions.length = n)
  (a : Nat)
  (b : Nat)
  (h4 : a = starting_positions.foldl min (starting_positions.head!))
  (h5 : b = starting_positions.foldl max (starting_positions.head!) + n * l) :
  let result := solve_snake_parade n l a b starting_positions
  result ≥ 0 ∧ result ≤ (b - a) * n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem snake_parade_sorted_optimal
  (n l : Nat)
  (start : Nat)
  (h1 : n > 0)
  (h2 : l > 0) :
  let positions := List.range n |>.map (fun i => start + i * l)
  solve_snake_parade n l start (start + n * l) positions = 0 := sorry

theorem snake_parade_order_invariant
  (starting_positions : List Nat)
  (l : Nat)
  (h1 : starting_positions.length > 0)
  (h2 : l > 0)
  (a : Nat)
  (b : Nat)
  (h3 : a = starting_positions.foldl min (starting_positions.head!))
  (h4 : b = starting_positions.foldl max (starting_positions.head!) + starting_positions.length * l) :
  let n := starting_positions.length
  ∀ perm : List Nat, perm.length = starting_positions.length →
  solve_snake_parade n l a b starting_positions =
  solve_snake_parade n l a b perm := sorry
-- </vc-theorems>