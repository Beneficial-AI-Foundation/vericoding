-- <vc-preamble>
def list_max (l: List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl Nat.max x xs

/- Function that returns the weight of the last remaining stone after smashing -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def last_stone_weight (stones : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_stone_identity (stone : Nat)
  (h : stone > 0 ∧ stone ≤ 1000) :
  last_stone_weight [stone] = stone := sorry

theorem identical_pair_zero (stone : Nat)
  (h : stone > 0 ∧ stone ≤ 1000) :
  last_stone_weight [stone, stone] = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval last_stone_weight [2, 7, 4, 1, 8, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval last_stone_weight [1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval last_stone_weight [2, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible