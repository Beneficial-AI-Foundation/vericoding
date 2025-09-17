-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_and_min (arr1 arr2 : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_and_min_output_size {arr1 arr2 : List Int} 
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) : 
  let result := max_and_min arr1 arr2
  result.length = 2 :=
sorry

theorem max_and_min_order {arr1 arr2 : List Int}
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  let result := max_and_min arr1 arr2
  result[0]! ≥ result[1]! :=
sorry

theorem max_and_min_nonneg {arr1 arr2 : List Int}
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  let result := max_and_min arr1 arr2
  result[0]! ≥ 0 ∧ result[1]! ≥ 0 :=
sorry

/-
info: [17, 2]
-/
-- #guard_msgs in
-- #eval max_and_min [3, 10, 5] [20, 7, 15, 8]

/-
info: [17, 17]
-/
-- #guard_msgs in
-- #eval max_and_min [3] [20]

/-
info: [9, 1]
-/
-- #guard_msgs in
-- #eval max_and_min [1, 2, 3, 4, 5] [6, 7, 8, 9, 10]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible