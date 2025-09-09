def solve (arr : List Int) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def List.isPermutationOf (l1 l2 : List Int) : Prop :=
  ∀ x, (l1.filter (· = x)).length = (l2.filter (· = x)).length

theorem solve_output_length {arr : List Int} (h : arr ≠ []) :
  (solve arr).length = arr.length :=
sorry

theorem solve_contains_same_elements {arr : List Int} (h : arr ≠ []) :
  (solve arr).isPermutationOf arr :=
sorry

theorem solve_maintains_frequency_order {arr : List Int} (h : arr ≠ []) :
  let freq := fun x => (arr.filter (· = x)).length
  ∀ i, i + 1 < (solve arr).length →
    let curr := (solve arr).get! i
    let next := (solve arr).get! (i+1)
    freq curr > freq next ∨ 
    (freq curr = freq next ∧ curr ≤ next) :=
sorry

theorem solve_idempotent {arr : List Int} (h : arr ≠ []) :
  solve (solve arr) = solve arr :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval solve [2, 3, 5, 3, 7, 9, 5, 3, 7]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval solve [1, 2, 3, 0, 5, 0, 1, 6, 8, 8, 6, 9, 1]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval solve [5, 9, 6, 9, 6, 5, 9, 9, 4, 4]

-- Apps difficulty: introductory
-- Assurance level: unguarded