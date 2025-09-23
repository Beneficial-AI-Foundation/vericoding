-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_chef_paint (arr : List Int) : String := sorry

theorem can_chef_paint_returns_valid_response {arr : List Int} (h : arr.length ≥ 3) :
  can_chef_paint arr = "Yes" ∨ can_chef_paint arr = "No" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_chef_paint_valid_inputs {arr : List Int} (h1 : arr.length ≥ 3)
  (h2 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 5) :
  (∃ i, i ≥ 1 ∧ i < arr.length - 1 ∧ 
    arr[i-1]! = arr[i]! ∧ arr[i]! = arr[i+1]!) ↔ 
  can_chef_paint arr = "Yes" := sorry

theorem can_chef_paint_array_bounds {arr : List Int} 
  (h1 : arr.length ≥ 3) (h2 : arr.length ≤ 10) :
  can_chef_paint arr = "Yes" → 
  ∃ i, i ≥ 1 ∧ i < arr.length - 1 ∧ 
    arr[i-1]! = arr[i]! ∧ arr[i]! = arr[i+1]! := sorry
-- </vc-theorems>