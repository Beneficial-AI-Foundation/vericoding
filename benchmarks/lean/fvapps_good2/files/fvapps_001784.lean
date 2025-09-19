-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fallingSquares (positions: List (List Int)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
variable (positions : List (List Int))
variable (result : List Int := fallingSquares positions)

theorem result_length :
  result.length = positions.length := 
sorry

theorem heights_monotonic {i : Nat} (h : i + 1 < result.length) :
  match result[i]?, result[i+1]? with
  | some x, some y => x ≥ 0 ∧ y ≥ x
  | _, _ => False
  := 
sorry

theorem heights_geq_sides :
  ∀ (i : Nat) (h : i < positions.length),
  match positions[i]?, result[i]? with
  | some pos, some height =>
    match pos.get? 1 with
    | some side => height ≥ side
    | none => True
  | _, _ => True 
  := 
sorry

theorem max_height_bound (sides : List Int) :
  (∀ i < positions.length,
    match positions[i]?, sides.get? i with
    | some pos, some side => pos.get? 1 = some side
    | _, _ => False) →
  result.length > 0 →
  ∀ h ∈ result, h ≤ sides.foldl (·+·) 0 := 
sorry

theorem results_nonneg :
  ∀ x ∈ result, x ≥ 0 := 
sorry
-- </vc-theorems>