-- <vc-helpers>
-- </vc-helpers>

def sort_array (arr : List Int) : List Int := sorry

def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

theorem sort_array_preserves_evens (arr : List Int) : 
  let result := sort_array arr
  List.length arr = List.length result ∧
  ∀ i, i < arr.length → 
    (arr[i]! % 2 = 0 → result[i]! = arr[i]!) := sorry

theorem sort_array_sorts_odds (arr : List Int) :
  let result := sort_array arr
  let odds := result.filter (fun x => x % 2 ≠ 0)
  isSorted odds := sorry

theorem sort_array_preserves_odd_count (arr : List Int) :
  let result := sort_array arr
  (arr.filter (fun x => x % 2 ≠ 0)).length = 
  (result.filter (fun x => x % 2 ≠ 0)).length := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval sort_array [5, 3, 2, 8, 1, 4]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sort_array [2, 22, 37, 11, 4, 1, 5, 0]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval sort_array [1, 2, 3, 4, 5, 6, 7, 8, 9, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded