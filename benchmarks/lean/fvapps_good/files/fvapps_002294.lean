-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def peak_index_in_mountain_array (arr : List Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem peak_index_not_at_edges {arr : List Int} (h: arr.length ≥ 3)
  (hm: ∃ i, 0 < i ∧ i < arr.length - 1 ∧ 
    (∀ j < i, arr[j]! < arr[j+1]!) ∧ 
    (∀ j, i ≤ j ∧ j < arr.length - 1 → arr[j]! > arr[j+1]!)) :
  let peak := peak_index_in_mountain_array arr
  0 < peak ∧ peak < arr.length - 1 :=
sorry

theorem peak_greater_than_left {arr : List Int} (h: arr.length ≥ 3)
  (hm: ∃ i, 0 < i ∧ i < arr.length - 1 ∧ 
    (∀ j < i, arr[j]! < arr[j+1]!) ∧ 
    (∀ j, i ≤ j ∧ j < arr.length - 1 → arr[j]! > arr[j+1]!)) :
  let peak := peak_index_in_mountain_array arr
  arr[peak]! > arr[peak-1]! :=
sorry

theorem peak_greater_than_right {arr : List Int} (h: arr.length ≥ 3) 
  (hm: ∃ i, 0 < i ∧ i < arr.length - 1 ∧ 
    (∀ j < i, arr[j]! < arr[j+1]!) ∧ 
    (∀ j, i ≤ j ∧ j < arr.length - 1 → arr[j]! > arr[j+1]!)) :
  let peak := peak_index_in_mountain_array arr
  arr[peak]! > arr[peak+1]! :=
sorry
-- </vc-theorems>