-- <vc-helpers>
-- </vc-helpers>

def max_friendships (friend_days : List Int) : Nat :=
  sorry

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

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_friendships [3, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_friendships [1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_friendships [4, 4, 5, 5, 5]

-- Apps difficulty: interview
-- Assurance level: guarded