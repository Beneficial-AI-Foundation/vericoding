-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_neighbors (arr : List (List Char)) (i j : Nat) : List Char := sorry

def land_perimeter (arr : List (List Char)) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>