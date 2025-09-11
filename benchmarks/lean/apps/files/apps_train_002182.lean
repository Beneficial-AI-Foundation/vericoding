-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tree_tag (n a b da db : Nat) (edges : List (Nat × Nat)) : String := sorry

-- Type safety - result must be one of two valid strings
-- </vc-definitions>

-- <vc-theorems>
theorem solve_tree_tag_valid_output
  (n a b da db : Nat) (edges : List (Nat × Nat)) :
  solve_tree_tag n a b da db edges = "Alice" ∨ 
  solve_tree_tag n a b da db edges = "Bob" := sorry

-- Alice wins if she can move twice as fast as Bob

theorem alice_wins_2x_speed 
  (n a b da db : Nat) (edges : List (Nat × Nat)) :
  2 * da ≥ db →
  solve_tree_tag n a b da db edges = "Alice" := sorry

/-
info: 'Alice'
-/
-- #guard_msgs in
-- #eval solve_tree_tag 4 3 2 1 2 [(1, 2), (1, 3), (1, 4)]

/-
info: 'Bob'
-/
-- #guard_msgs in
-- #eval solve_tree_tag 6 6 1 2 5 [(1, 2), (6, 5), (2, 3), (3, 4), (4, 5)]

/-
info: 'Alice'
-/
-- #guard_msgs in
-- #eval solve_tree_tag 5 5 4 3 4 [(1, 2), (4, 1), (5, 1), (5, 3)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded