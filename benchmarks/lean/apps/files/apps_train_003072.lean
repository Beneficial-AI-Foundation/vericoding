-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def length_of_sequence (arr : List Int) (n : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_of_sequence_non_negative (arr : List Int) (n : Int) :
  length_of_sequence arr n ≥ 0 :=
  sorry 

theorem length_of_sequence_exactly_two_occurrences (arr : List Int) (n : Int) :
  (arr.count n = 2) →
  length_of_sequence arr n > 0 ∧
  ∃ first second : Nat,
    first < arr.length ∧
    second < arr.length ∧
    second > first ∧ 
    arr[first]! = n ∧
    arr[second]! = n ∧
    length_of_sequence arr n = second - first + 1 :=
  sorry

theorem length_of_sequence_not_two_occurrences (arr : List Int) (n : Int) :
  (arr.count n ≠ 2) →
  length_of_sequence arr n = 0 :=
  sorry

theorem length_of_sequence_adjacent_elements {arr : List Int} {n : Int} 
  (h : arr.length ≥ 1) : 
  let arr' := n :: arr
  (arr'.count n = 2) →
  length_of_sequence arr' n = 2 :=
  sorry

theorem length_of_sequence_missing_element {arr : List Int} (n : Int)
  (h : ∀ x ∈ arr, x < n) :
  length_of_sequence arr n = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval length_of_sequence [1] 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval length_of_sequence [1] 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval length_of_sequence [-7, 3, -7, -7, 2, 1] -7

/-
info: 5
-/
-- #guard_msgs in
-- #eval length_of_sequence [0, -3, 7, 4, 0, 3, 7, 9] 7
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded