-- <vc-preamble>
def DSU.merge (dsu : DSU n) (a b : Nat) : Nat := sorry
def DSU.leader (dsu : DSU n) (a : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_game (n m : Nat) (required gain : Array Int) (edges : Array (Nat × Nat)) : Int := sorry

theorem single_node_property (n : Nat) :
  n > 0 →
  solve_game 1 0 #[n] #[0] #[] = n := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_game 4 5 #[3, 1, 4, 6] #[1, 2, 1, 2] #[(1, 2), (2, 3), (2, 4), (1, 4), (3, 4)]

/-
info: 44
-/
-- #guard_msgs in
-- #eval solve_game 5 8 #[6, 15, 15, 15, 20] #[4, 13, 19, 1, 7] #[(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 5), (4, 5)]

/-
info: 582
-/
-- #guard_msgs in
-- #eval solve_game 9 10 #[131, 98, 242, 231, 382, 224, 140, 209, 164] #[2, 79, 32, 38, 82, 22, 88, 70, 64] #[(6, 8), (1, 6), (1, 4), (1, 3), (4, 7), (4, 9), (3, 7), (3, 9), (5, 9), (2, 5)]
-- </vc-theorems>