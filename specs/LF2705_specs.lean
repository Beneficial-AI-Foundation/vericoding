-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs

def List.minimum : List Nat → Nat
  | [] => 0 
  | [x] => x
  | x::xs => Nat.min x (minimum xs)

def pack_bagpack (scores weights : List Nat) (capacity : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_valid_score (scores weights : List Nat) (capacity : Nat) : Nat :=
  let pairs := List.zip scores weights
  let valid := List.filter (fun p => p.snd ≤ capacity) pairs
  let scores := List.map Prod.fst valid
  match scores with
  | [] => 0
  | x::xs => List.foldl Nat.max x xs
-- </vc-definitions>

-- <vc-theorems>
theorem pack_backpack_non_negative (scores weights : List Nat) (capacity : Nat) :
  pack_bagpack scores weights capacity ≥ 0 := sorry

theorem pack_backpack_at_most_sum_scores (scores weights : List Nat) (capacity : Nat) :
  pack_bagpack scores weights capacity ≤ List.sum scores := sorry

theorem pack_backpack_zero_if_capacity_too_small 
  (scores weights : List Nat) (capacity : Nat)
  (h : capacity < List.minimum weights) :
  pack_bagpack scores weights capacity = 0 := sorry

theorem pack_backpack_at_least_max_valid_score 
  (scores weights : List Nat) (capacity : Nat)
  (h : scores.length = weights.length)
  (h2 : scores.length > 0) :
  pack_bagpack scores weights capacity ≥ max_valid_score scores weights capacity := sorry

/-
info: 29
-/
-- #guard_msgs in
-- #eval pack_bagpack [15, 10, 9, 5] [1, 5, 3, 4] 8

/-
info: 60
-/
-- #guard_msgs in
-- #eval pack_bagpack [20, 5, 10, 40, 15, 25] [1, 2, 3, 8, 7, 4] 10

/-
info: 39
-/
-- #guard_msgs in
-- #eval pack_bagpack [100, 5, 16, 18, 50] [25, 1, 3, 2, 15] 14
-- </vc-theorems>