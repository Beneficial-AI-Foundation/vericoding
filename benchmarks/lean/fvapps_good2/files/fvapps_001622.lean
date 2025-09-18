-- <vc-preamble>
def Graph := List (List Nat)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_graph (g : Graph) : Bool :=
sorry

def find_most_popular_friend (friend_lists : List String) : Nat × Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem most_popular_friend_bounds (friend_lists : List String)
  (h : friend_lists.length > 0) :
  let (popular, notoriety) := find_most_popular_friend friend_lists
  1 ≤ popular ∧ popular ≤ friend_lists.length :=
sorry

theorem notoriety_bounds (friend_lists : List String)
  (h : friend_lists.length > 0) :
  let (popular, notoriety) := find_most_popular_friend friend_lists
  0 ≤ notoriety ∧ notoriety ≤ Float.ofNat friend_lists.length :=
sorry
-- </vc-theorems>