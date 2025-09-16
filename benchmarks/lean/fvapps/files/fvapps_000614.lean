-- <vc-preamble>
def find_tallest_mountain (n : Nat) (heights : List Nat) : Nat :=
sorry

def list_max (l : List Nat) : Nat :=
match l with
| [] => 0
| h::t => List.foldl Nat.max h t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_min (l : List Nat) : Nat :=
match l with
| [] => 0
| h::t => List.foldl Nat.min h t
-- </vc-definitions>

-- <vc-theorems>
theorem find_tallest_in_list {n : Nat} {heights : List Nat} (h : heights ≠ []) :
  find_tallest_mountain n heights ∈ heights
  := sorry

theorem length_preserved {n : Nat} {heights : List Nat} :
  heights.length = n →
  heights.length = n
  := sorry

theorem single_mountain_height {height : Nat} :
  find_tallest_mountain 1 [height] = height
  := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_tallest_mountain 5 [4, 7, 6, 3, 1]

/-
info: 30
-/
-- #guard_msgs in
-- #eval find_tallest_mountain 3 [10, 20, 30]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_tallest_mountain 1 [5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible