-- <vc-helpers>
-- </vc-helpers>

def greatest_distance (lst: List Int) : Nat :=
  sorry

theorem greatest_distance_nonnegative (lst: List Int) : 
  greatest_distance lst ≥ 0 :=
sorry

theorem greatest_distance_duplicate_lower_bound {lst : List Int} {i j : Nat} : 
  i < j → j < lst.length → 
  (h1 : i < lst.length) → (h2 : j < lst.length) →
  lst.get ⟨i, h1⟩ = lst.get ⟨j, h2⟩ → 
  greatest_distance lst ≥ j - i :=
sorry

theorem greatest_distance_unique_list {lst : List Int} : 
  lst.Nodup → greatest_distance lst = 0 :=
sorry

theorem greatest_distance_repeated_element (x : Int) :
  greatest_distance [x, x, x] = 2 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval greatest_distance [9, 7, 1, 2, 3, 7, 0, -1, -2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval greatest_distance [0, 7, 0, 2, 3, 7, 0, -1, -2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval greatest_distance [1, 2, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible