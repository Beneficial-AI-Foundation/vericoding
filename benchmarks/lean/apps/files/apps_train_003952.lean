def count_range_collapses (arr : List Int) : Nat := sorry

def is_power_of_two (n : Nat) : Bool := 
  (n &&& (n - 1) = 0) && n > 0

def count_consecutive_pairs (l : List Int) : Nat :=
  let pairs := l.zip (l.drop 1)
  pairs.foldl (fun acc p => if p.2 - p.1 = 1 then acc + 1 else acc) 0

-- <vc-helpers>
-- </vc-helpers>

def sort_list (l : List Int) : List Int :=
  l.mergeSort (fun a b => a ≤ b)

theorem non_consecutive_array_returns_one 
  {arr : List Int} (h : arr.length > 0) :
  (∀ i, i + 1 < arr.length → arr[i]! + 1 < arr[i+1]!) → 
  count_range_collapses arr = 1 := sorry

theorem result_is_power_of_two 
  {arr : List Int} (h : arr.length > 1) :
  is_power_of_two (count_range_collapses arr) := sorry

theorem consecutive_pairs_determine_result
  {arr : List Int} (h : arr.length > 1) :
  let sorted := sort_list arr
  let consec_count := count_consecutive_pairs sorted
  count_range_collapses arr = 2 ^ consec_count := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_range_collapses [1, 3, 4, 5, 6, 8]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_range_collapses [1, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_range_collapses [11, 43, 66, 123]

-- Apps difficulty: introductory
-- Assurance level: guarded