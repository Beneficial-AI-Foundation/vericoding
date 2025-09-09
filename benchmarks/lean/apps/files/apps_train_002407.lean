def max_freq (l: List Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def find_shortest_subarray (l : List Int) : Nat :=
  sorry

theorem shortest_subarray_bounds {l : List Int} (h: l ≠ []) :
  1 ≤ find_shortest_subarray l ∧ find_shortest_subarray l ≤ l.length :=
  sorry

theorem single_element_list {l : List Int} (h: l.length = 1) :
  find_shortest_subarray l = 1 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_shortest_subarray [1, 2, 2, 3, 1]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_shortest_subarray [1, 2, 2, 3, 1, 4, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_shortest_subarray [1, 1, 2, 2, 2, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible