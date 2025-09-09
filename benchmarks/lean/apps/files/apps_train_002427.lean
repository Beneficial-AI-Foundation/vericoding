-- <vc-helpers>
-- </vc-helpers>

def numIdenticalPairs (nums : List Int) : Nat := sorry

theorem num_identical_pairs_non_negative (nums : List Int) :
  numIdenticalPairs nums ≥ 0 := sorry

theorem empty_or_single_is_zero (nums : List Int) :
  nums.length ≤ 1 → numIdenticalPairs nums = 0 := sorry

theorem all_same_values (nums : List Int) (n : Nat) (x : Int) :
  nums = List.replicate n x → n ≥ 2 →
  numIdenticalPairs nums = n * (n-1) / 2 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval numIdenticalPairs [1, 2, 3, 1, 1, 3]

/-
info: 6
-/
-- #guard_msgs in
-- #eval numIdenticalPairs [1, 1, 1, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numIdenticalPairs [1, 2, 3]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible