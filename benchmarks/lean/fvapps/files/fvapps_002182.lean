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
-- </vc-theorems>