/-
Task:
Given an array arr of strings complete the function landPerimeter by calculating the total perimeter of all the islands. Each piece of land will be marked with 'X' while the water fields are represented as 'O'. Consider each tile being a perfect 1 x 1piece of land. Some examples for better visualization:

['XOOXO',
  'XOOXO',
  'OOOXO',
  'XXOXO',
  'OXOOO'] 

or 

should return:
"Total land perimeter: 24",

while

['XOOO',
  'XOXO',
  'XOXO',
  'OOXX',
  'OOOO']

should return: "Total land perimeter: 18"
Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def get_neighbors (arr : List (List Char)) (i j : Nat) : List Char := sorry

def land_perimeter (arr : List (List Char)) : String := sorry

theorem land_perimeter_output_format {arr : List (List Char)}
  (h1 : ∀ row ∈ arr, ∀ c ∈ row, c = 'X' ∨ c = 'O')
  (h2 : ∀ row ∈ arr, row.length = arr[0]!.length)
  (h3 : arr.length > 0 ∧ arr.length ≤ 10)
  (h4 : arr[0]!.length > 0 ∧ arr[0]!.length ≤ 10) :
  ∃ n : Nat, land_perimeter arr = "Total land perimeter: " ++ toString n := sorry

theorem perimeter_multiple_of_four_for_isolated_lands {arr : List (List Char)}
  (h1 : ∀ row ∈ arr, ∀ c ∈ row, c = 'X' ∨ c = 'O')
  (h2 : ∀ row ∈ arr, row.length = arr[0]!.length)
  (h3 : arr.length > 0 ∧ arr.length ≤ 10)
  (h4 : arr[0]!.length > 0 ∧ arr[0]!.length ≤ 10)
  (h5 : ∀ i j, i < arr.length → j < arr[0]!.length →
        arr[i]![j]! = 'O' ∨
        (arr[i]![j]! = 'X' ∧ 
         ∀ n ∈ get_neighbors arr i j, n = 'O')) :
  ∃ n : Nat, land_perimeter arr = "Total land perimeter: " ++ toString n ∧ n % 4 = 0 := sorry

theorem zero_perimeter_for_empty_land {arr : List (List Char)}
  (h1 : ∀ row ∈ arr, ∀ c ∈ row, c = 'O')
  (h2 : ∀ row ∈ arr, row.length = arr[0]!.length)
  (h3 : arr.length > 0 ∧ arr.length ≤ 10)
  (h4 : arr[0]!.length > 0 ∧ arr[0]!.length ≤ 10) :
  land_perimeter arr = "Total land perimeter: 0" := sorry

/-
info: 'Total land perimeter: 24'
-/
-- #guard_msgs in
-- #eval land_perimeter ["XOOXO", "XOOXO", "OOOXO", "XXOXO", "OXOOO"]

/-
info: 'Total land perimeter: 18'
-/
-- #guard_msgs in
-- #eval land_perimeter ["XOOO", "XOXO", "XOXO", "OOXX", "OOOO"]

/-
info: 'Total land perimeter: 4'
-/
-- #guard_msgs in
-- #eval land_perimeter ["X"]

-- Apps difficulty: introductory
-- Assurance level: unguarded