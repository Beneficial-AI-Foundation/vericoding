-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def logistic_map (width height : Nat) (xs ys : List Nat) : List (List (Option Nat)) := sorry

theorem logistic_map_dimensions (width height : Nat) (xs ys : List Nat) :
  let result := logistic_map width height xs ys
  result.length = height ∧ 
  ∀ row ∈ result, row.length = width := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem logistic_map_empty_input (width height : Nat) :
  let result := logistic_map width height [] []
  ∀ row ∈ result, ∀ cell ∈ row, cell = none := sorry

theorem logistic_map_supply_points (width height : Nat) (xs ys : List Nat) :
  ∀ (x y : Nat), x ∈ xs → y ∈ ys → x < width → y < height →
  (logistic_map width height xs ys).get? y >>= (·.get? x) = some (some 0) := sorry

theorem logistic_map_triangle_inequality (width height : Nat) (xs ys : List Nat) :
  let result := logistic_map width height xs ys
  (∀ y < height, ∀ x < width - 1,
    ∀ v1 v2, result.get? y >>= (·.get? x) = some (some v1) → 
    result.get? y >>= (·.get? (x+1)) = some (some v2) → 
    v1 ≤ v2 + 1 ∧ v2 ≤ v1 + 1) ∧
  (∀ y < height - 1, ∀ x < width,
    ∀ v1 v2, result.get? y >>= (·.get? x) = some (some v1) → 
    result.get? (y+1) >>= (·.get? x) = some (some v2) →
    v1 ≤ v2 + 1 ∧ v2 ≤ v1 + 1) := sorry

theorem logistic_map_single_point (width height : Nat) :
  let result := logistic_map width height [0] [0]
  width > 0 → height > 0 →
  result.get? 0 >>= (·.get? 0) = some (some 0) ∧
  ∀ y < height, ∀ x < width,
    result.get? y >>= (·.get? x) = some (some (x + y)) := sorry
-- </vc-theorems>