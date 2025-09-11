-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fallingSquares (positions: List (List Int)) : List Int :=
  sorry

variable (positions : List (List Int))
variable (result : List Int := fallingSquares positions)

/- Result length should match input length -/
-- </vc-definitions>

-- <vc-theorems>
theorem result_length : 
  result.length = positions.length := sorry

/- Heights are monotonically non-decreasing -/

theorem heights_monotonic {i : Nat} (h : i + 1 < result.length) :
  match result[i]?, result[i+1]? with
  | some x, some y => x ≥ 0 ∧ y ≥ x
  | _, _ => False
  := sorry

/- Each height is at least as tall as corresponding square -/

theorem heights_geq_sides : 
  ∀ (i : Nat) (h : i < positions.length), 
  match positions[i]?, result[i]? with
  | some pos, some height => 
    match pos.get? 1 with
    | some side => height ≥ side
    | none => True
  | _, _ => True
  := sorry

/- Maximum height is bounded by sum of all side lengths -/

theorem max_height_bound (sides : List Int) :
  (∀ i < positions.length, 
    match positions[i]?, sides.get? i with 
    | some pos, some side => pos.get? 1 = some side
    | _, _ => False) →
  result.length > 0 →
  ∀ h ∈ result, h ≤ sides.foldl (·+·) 0 := sorry

/- Results are non-negative integers -/

theorem results_nonneg : 
  ∀ x ∈ result, x ≥ 0 := sorry

/-
info: [2, 5, 5]
-/
-- #guard_msgs in
-- #eval fallingSquares [[1, 2], [2, 3], [6, 1]]

/-
info: [100, 100]
-/
-- #guard_msgs in
-- #eval fallingSquares [[100, 100], [200, 100]]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval fallingSquares [[1, 2], [3, 1]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded