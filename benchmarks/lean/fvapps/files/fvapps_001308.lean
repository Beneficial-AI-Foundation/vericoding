-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_transform (n : Nat) (arr : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_transform_length {n : Nat} {arr : List Nat} 
  (h : n > 0) (h2 : arr.length > 0) :
  (solve_array_transform n arr).length = n :=
sorry

theorem array_transform_elements {n : Nat} {arr : List Nat} 
  (h : n > 0) (h2 : arr.length > 0) :
  ∀ i, i ∈ (solve_array_transform n arr) → Nat.le 1 i :=
sorry

theorem array_transform_valid_indices {n : Nat} {arr : List Nat}
  (h : n > 0) (h2 : arr.length = n) :
  ∀ i, i < n → arr[i]! ≤ n → 
    (solve_array_transform n arr)[i]! = arr[i]! + arr[arr[i]! - 1]! :=
sorry

theorem array_transform_single {n : Nat} 
  (h : n > 0) :
  let arr := List.replicate n 1
  (solve_array_transform n arr)[0]! = 2 :=
sorry

theorem array_transform_sequential {n : Nat}
  (h : n > 0) :
  let arr := List.range n |>.map (·+1)
  ∀ i, i < n → arr[i]! ≤ n →
    (solve_array_transform n arr)[i]! = arr[i]! + arr[arr[i]! - 1]! :=
sorry
-- </vc-theorems>