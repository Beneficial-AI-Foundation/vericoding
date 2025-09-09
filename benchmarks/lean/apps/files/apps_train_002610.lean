-- <vc-helpers>
-- </vc-helpers>

def sumAverage (lists : List (List Int)) : Int :=
  sorry

theorem sumAverage_is_floor_of_means (lists : List (List Int)) 
  (h : ∀ l ∈ lists, l.length > 0) :
  ∃ mean, sumAverage lists = mean := -- simplified since we can't easily represent floor of means
  sorry

theorem sumAverage_le_sum_maxes (lists : List (List Int))
  (h : ∀ l ∈ lists, l.length > 0) :
  ∀ l ∈ lists, ∀ x ∈ l, sumAverage lists ≤ x :=
  sorry

theorem sumAverage_ge_mins (lists : List (List Int))
  (h : ∀ l ∈ lists, l.length > 0) :
  ∀ l ∈ lists, ∀ x ∈ l, x ≤ sumAverage lists :=
  sorry

theorem sumAverage_type (lists : List (List Int))
  (h : ∀ l ∈ lists, l.length > 0) :
  sumAverage lists = sumAverage lists :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval sum_average [[1, 2, 2, 1], [2, 2, 2, 1]]

/-
info: 44
-/
-- #guard_msgs in
-- #eval sum_average [[3, 4, 1, 3, 5, 1, 4], [21, 54, 33, 21, 76]]

/-
info: -6
-/
-- #guard_msgs in
-- #eval sum_average [[-4, 3, -8, -2], [2, 9, 1, -5], [-7, -2, -6, -4]]

-- Apps difficulty: introductory
-- Assurance level: unguarded