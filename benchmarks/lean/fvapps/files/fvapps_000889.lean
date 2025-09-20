-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_friendships (friend_days : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_friendships_upper_bound (friend_days : List Int) (h : friend_days ≠ []) :
  max_friendships friend_days ≤ friend_days.length := 
  sorry

theorem max_friendships_at_least_one (friend_days : List Int) (h : friend_days ≠ []) :
  max_friendships friend_days ≥ 1 :=
  sorry

theorem max_friendships_idempotent (friend_days : List Int) (h : friend_days ≠ []) :
  max_friendships friend_days = max_friendships friend_days :=
  sorry

theorem max_friendships_duplicate_invariant (friend_days : List Int) (h : friend_days ≠ []) :
  max_friendships friend_days = max_friendships (friend_days ++ [List.head! friend_days]) :=
  sorry

theorem max_friendships_new_element_bound (friend_days : List Int) (new_day : Int) (h : friend_days ≠ []) :
  max_friendships (friend_days ++ [new_day]) ≤ max_friendships friend_days + 1 :=
  sorry
-- </vc-theorems>