-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def moveZeros {α} [BEq α] (arr : List α) (isZero : α → Bool) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem moveZeros_bool_preserves_false (arr : List Bool) :
  let result := moveZeros arr (· = false)
  (arr.filter (· = false)).length = (result.filter (· = false)).length := by
    sorry

theorem moveZeros_preserves_length {α} [BEq α] (arr : List α) (isZero : α → Bool) :
  (moveZeros arr isZero).length = arr.length := by
    sorry

theorem moveZeros_preserves_nonzeros {α} [BEq α] (arr : List α) (isZero : α → Bool) :
  (arr.filter (not ∘ isZero)) = ((moveZeros arr isZero).filter (not ∘ isZero)) := by
    sorry

theorem moveZeros_preserves_zero_count {α} [BEq α] (arr : List α) (isZero : α → Bool) :
  (arr.filter isZero).length = ((moveZeros arr isZero).filter isZero).length := by
    sorry
-- </vc-theorems>