-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_the_missing_tree (numbers : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_in_input (numbers : List Int) (h : numbers.length > 0):
  let doubled_numbers := numbers ++ numbers
  let input_list := doubled_numbers.dropLast
  let result := find_the_missing_tree input_list
  result ∈ input_list :=
sorry

theorem result_appears_least (numbers : List Int) (h : numbers.length ≥ 3):
  let tripled := numbers ++ numbers ++ numbers  
  let input_list := (tripled.take (tripled.length / 2)) ++ (tripled.drop (tripled.length / 2 + 1))
  let result := find_the_missing_tree input_list
  ∀ n ∈ input_list, (input_list.count result) ≤ (input_list.count n) :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_the_missing_tree [1, 2, 2, 3, 3]

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_the_missing_tree [2, 2, 2, 56, 56, 56, 8, 8]

/-
info: 64
-/
-- #guard_msgs in
-- #eval find_the_missing_tree [34, 76, 12, 99, 64, 99, 76, 12, 34]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible