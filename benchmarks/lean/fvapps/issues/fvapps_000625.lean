-- <vc-preamble>
def List.sum : List Nat → Nat 
| [] => 0
| (h :: t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_share_candies (n_friends : Nat) (candies : List Nat) : String := sorry

theorem can_share_candies_valid_output (n_friends : Nat) (candies : List Nat) 
  (h1 : n_friends > 0) (h2 : candies.length > 0) :
  (can_share_candies n_friends candies = "Yes" ∨ 
   can_share_candies n_friends candies = "No") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_share_candies_yes_iff_divisible (n_friends : Nat) (candies : List Nat)
  (h1 : n_friends > 0) (h2 : candies.length > 0) :
  can_share_candies n_friends candies = "Yes" ↔ 
  (List.sum candies % n_friends = 0) := sorry

theorem single_friend_always_yes (candies : List Nat) (h : candies.length > 0) :
  can_share_candies 1 candies = "Yes" := sorry

theorem zero_list_evenly_divisible (n_friends : Nat) (h : n_friends > 1) :
  can_share_candies n_friends [0] = "Yes" := sorry

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_share_candies 3 [1, 2, 3]

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval can_share_candies 2 [1, 2]

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_share_candies 4 [2, 2, 2, 2]
-- </vc-theorems>