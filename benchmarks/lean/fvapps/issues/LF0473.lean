-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxArea (heights : List Nat) : Nat := sorry

theorem maxArea_nonnegative (heights : List Nat) :
  heights.length ≥ 2 → maxArea heights ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxArea_upper_bound (heights : List Nat) :
  heights.length ≥ 2 → 
  maxArea heights ≤ (List.maximum? heights).getD 0 * (heights.length - 1) := sorry

theorem maxArea_is_maximum (heights : List Nat) (i j : Nat) (hi : i < heights.length) (hj : j < heights.length) :
  heights.length ≥ 2 →
  i < j →
  maxArea heights ≥ min (heights.get ⟨i, hi⟩) (heights.get ⟨j, hj⟩) * (j - i) := sorry

theorem maxArea_symmetric (heights : List Nat) :
  heights.length ≥ 2 →
  maxArea heights = maxArea heights.reverse := sorry

theorem maxArea_uniform (value length : Nat) : 
  length ≥ 2 →
  maxArea (List.replicate length value) = value * (length - 1) := sorry

theorem maxArea_interpolation (heights : List Nat) :
  heights.length ≥ 2 →
  let interpolated := heights.take 1 ++ List.replicate (heights.length - 2) 0 ++ heights.drop (heights.length - 1)
  maxArea heights ≥ maxArea interpolated := sorry

/-
info: 49
-/
-- #guard_msgs in
-- #eval max_area [1, 8, 6, 2, 5, 4, 8, 3, 7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_area [1, 1]

/-
info: 16
-/
-- #guard_msgs in
-- #eval max_area [4, 3, 2, 1, 4]
-- </vc-theorems>