-- <vc-preamble>
def isValidTree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxHappiness (n k : Nat) (edges : List (Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxHappiness_valid_tree (n : Nat) (k : Nat) 
  (edges : List (Nat × Nat)) :
  isValidTree n edges → True :=
sorry

theorem maxHappiness_nonnegative (n : Nat) (k : Nat)
  (edges : List (Nat × Nat)) :
  isValidTree n edges → maxHappiness n k edges ≥ 0 :=
sorry

theorem maxHappiness_zero_when_k_geq_n (n : Nat) (k : Nat)
  (edges : List (Nat × Nat)) :
  isValidTree n edges →
  k ≥ n →
  maxHappiness n k edges = 0 :=
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval max_happiness 7 4 [(1, 2), (1, 3), (1, 4), (3, 5), (3, 6), (4, 7)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_happiness 4 1 [(1, 2), (1, 3), (2, 4)]

/-
info: 9
-/
-- #guard_msgs in
-- #eval max_happiness 8 5 [(7, 5), (1, 7), (6, 1), (3, 7), (8, 3), (2, 1), (4, 5)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded