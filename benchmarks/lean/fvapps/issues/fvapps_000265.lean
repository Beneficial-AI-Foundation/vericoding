-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum xs

structure Box where
  n : Nat
  status : List Bool
  candies : List Nat
  keys : List (List Nat)
  contained_boxes : List (List Nat)
  initial_boxes : List Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxCandies (status : List Bool) (candies : List Nat) (keys : List (List Nat))
  (contained_boxes : List (List Nat)) (initial_boxes : List Nat) : Nat :=
  sorry

-- Result should be non-negative
-- </vc-definitions>

-- <vc-theorems>
theorem maxCandies_nonnegative 
  (status : List Bool) (candies : List Nat) (keys : List (List Nat))
  (contained_boxes : List (List Nat)) (initial_boxes : List Nat) :
  maxCandies status candies keys contained_boxes initial_boxes ≥ 0 := sorry

-- Result should not exceed sum of all candies

theorem maxCandies_upper_bound 
  (status : List Bool) (candies : List Nat) (keys : List (List Nat))
  (contained_boxes : List (List Nat)) (initial_boxes : List Nat) :
  maxCandies status candies keys contained_boxes initial_boxes ≤ List.sum candies := sorry

-- Result should be zero if no boxes are unlocked

theorem maxCandies_all_locked 
  (status : List Bool) (candies : List Nat) (keys : List (List Nat))
  (contained_boxes : List (List Nat)) (initial_boxes : List Nat) :
  (∀ s ∈ status, s = false) → 
  maxCandies status candies keys contained_boxes initial_boxes = 0 := sorry

/-
info: 16
-/
-- #guard_msgs in
-- #eval maxCandies [1, 0, 1, 0] [7, 5, 4, 100] [[], [], [1], []] [[1, 2], [3], [], []] [0]

/-
info: 6
-/
-- #guard_msgs in
-- #eval maxCandies [1, 0, 0, 0, 0, 0] [1, 1, 1, 1, 1, 1] [[1, 2, 3, 4, 5], [], [], [], [], []] [[1, 2, 3, 4, 5], [], [], [], [], []] [0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval maxCandies [1, 1, 1] [100, 1, 100] [[], [0, 2], []] [[], [], []] [1]
-- </vc-theorems>