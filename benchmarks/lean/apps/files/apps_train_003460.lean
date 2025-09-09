/-
In this Kata, you will be given an array of unique elements, and your task is to rerrange the values so that the first max value is followed by the first minimum, followed by second max value then second min value, etc. 

For example:
The first max is `15` and the first min is `7`. The second max is `12` and the second min is `10` and so on. 

More examples in the test cases. 

Good luck!
-/

def solve (arr : List Int) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_max (l : List Int) : Int :=
  sorry

theorem solve_maintains_elements {arr : List Int} (h : arr ≠ []) :
  let result := solve arr
  result.length = arr.length ∧ 
  ∀ x, (result.count x = arr.count x) :=
  sorry

theorem solve_alternates_high_low {arr : List Int} (h : arr.length ≥ 2) :
  let result := solve arr
  ∀ i, i + 1 < result.length → i % 2 = 0 → 
  (result.get ⟨i, sorry⟩) ≥ (result.get ⟨i+1, sorry⟩) :=
  sorry

theorem solve_first_element_is_max {arr : List Int} (h : arr ≠ []) :
  let result := solve arr
  ∀ i, i < result.length → 
  (result.get ⟨0, sorry⟩) ≥ (result.get ⟨i, sorry⟩) :=
  sorry

theorem solve_empty_and_single {arr : List Int} :
  arr.length ≤ 1 → solve arr = arr :=
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval solve [15, 11, 10, 7, 12]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval solve [91, 75, 86, 14, 82]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval solve [1, 6, 9, 4, 3, 7, 8, 2]

-- Apps difficulty: introductory
-- Assurance level: unguarded