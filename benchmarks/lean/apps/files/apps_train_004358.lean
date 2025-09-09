-- <vc-helpers>
-- </vc-helpers>

def moveZeros {α} [BEq α] (arr : List α) (isZero : α → Bool) : List α :=
  sorry

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

/-
info: expected1
-/
-- #guard_msgs in
-- #eval move_zeros [False, 1, 0, 1, 2, 0, 1, 3, "a"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval move_zeros [1, 2, 0, 1, 0, 1, 0, 3, 0, 1]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval move_zeros ["a", 0, 0, "b", "c", "d", 0, 1, 0, 1, 0, 3, 0, 1, 9, 0, 0, 0, 0, 9]

-- Apps difficulty: introductory
-- Assurance level: unguarded