-- <vc-helpers>
-- </vc-helpers>

def solve_marble_game (N : Nat) (parents : List Nat) : Nat := sorry

theorem single_parent_tree_bounds (N : Nat) (h : N ≥ 1) (h2 : N ≤ 100) : 
  let parents := List.replicate N 0
  let result := solve_marble_game N parents 
  0 ≤ result ∧ result < 10^9 + 7 := sorry

theorem linear_tree_bounds (N : Nat) (h : N ≥ 2) (h2 : N ≤ 100) :
  let parents := List.range N
  let result := solve_marble_game N parents
  0 ≤ result ∧ result < 10^9 + 7 := sorry

theorem balanced_binary_tree_bounds (N : Nat) (h : N ≥ 1) (h2 : N ≤ 100) :
  let parents := List.map (fun i => if i = 0 then 0 else (i-1)/2) (List.range N)
  let result := solve_marble_game N parents
  0 ≤ result ∧ result < 10^9 + 7 := sorry

theorem valid_parent_values (parents : List Nat) (h : parents.length ≥ 1) (h2 : parents.length ≤ 100) :
  let N := parents.length
  let bounded_parents := List.map (fun p => min p N) parents
  let result := solve_marble_game N bounded_parents
  0 ≤ result ∧ result < 10^9 + 7 := sorry

theorem modulo_property (N : Nat) (h : N ≥ 1) (h2 : N ≤ 100) :
  let parents := List.range N
  let result := solve_marble_game N parents
  0 ≤ result ∧ result < 10^9 + 7 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_marble_game 2 [0, 0]

/-
info: 96
-/
-- #guard_msgs in
-- #eval solve_marble_game 5 [0, 1, 1, 0, 4]

/-
info: 730395550
-/
-- #guard_msgs in
-- #eval solve_marble_game 31 [0, 1, 0, 2, 4, 0, 4, 1, 6, 4, 3, 9, 7, 3, 7, 2, 15, 6, 12, 10, 12, 16, 5, 3, 20, 1, 25, 20, 23, 24, 23]

-- Apps difficulty: competition
-- Assurance level: unguarded