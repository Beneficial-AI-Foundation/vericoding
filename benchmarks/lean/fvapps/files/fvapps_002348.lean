-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def valid_mountain_array (arr: List Int) : Bool := sorry

theorem too_short_array {arr : List Int} 
  (h : arr.length ≤ 2) : 
  valid_mountain_array arr = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flat_array {arr : List Int} {n : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3) 
  (h3 : ∀ i j, i < n → j < n → arr.get! i = arr.get! j) :
  valid_mountain_array arr = false := sorry

theorem strictly_increasing {arr : List Int} {n : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3)
  (h3 : ∀ i j, i < j → j < n → arr.get! i < arr.get! j) :
  valid_mountain_array arr = false := sorry

theorem strictly_decreasing {arr : List Int} {n : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3)  
  (h3 : ∀ i j, i < j → j < n → arr.get! i > arr.get! j) :
  valid_mountain_array arr = false := sorry

theorem valid_mountain {arr : List Int} {n peak_idx : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3)
  (h3 : peak_idx = n / 2)
  (h4 : ∀ i j, i < j → j < peak_idx → arr.get! i < arr.get! j)
  (h5 : ∀ i j, peak_idx < i → i < j → j < n → arr.get! i > arr.get! j)
  (h6 : ∀ i j, i ≠ j → i < n → j < n → arr.get! i ≠ arr.get! j) :
  valid_mountain_array arr = true := sorry
-- </vc-theorems>