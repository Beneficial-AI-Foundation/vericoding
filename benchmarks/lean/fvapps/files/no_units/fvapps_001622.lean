-- <vc-preamble>
def Graph := List (List Nat)
def is_valid_graph (g : Graph) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_most_popular_friend (friend_lists : List String) : Nat × Float := sorry

theorem most_popular_friend_bounds (friend_lists : List String) 
  (h : friend_lists.length > 0) :
  let (popular, notoriety) := find_most_popular_friend friend_lists
  1 ≤ popular ∧ popular ≤ friend_lists.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem notoriety_bounds (friend_lists : List String)
  (h : friend_lists.length > 0) :
  let (popular, notoriety) := find_most_popular_friend friend_lists 
  0 ≤ notoriety ∧ notoriety ≤ Float.ofNat friend_lists.length := sorry
-- </vc-theorems>