-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def soup_servings (n : Nat) : Float := sorry

theorem result_is_probability (n : Nat) :
  0 ≤ soup_servings n ∧ soup_servings n ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem large_inputs (n : Nat) (h : n ≥ 5001) :
  (soup_servings n - 1).abs < 0.000001 := sorry

theorem monotonic_increase (n delta : Nat) (h : n + delta ≤ 5000) :
  soup_servings n ≤ soup_servings (n + delta) := sorry

theorem symmetric_servings (n : Nat) (h : n ≤ 1000) :
  (soup_servings n - soup_servings n).abs = 0 := sorry

theorem boundary_value :
  (soup_servings 0 - 0.5).abs < 0.000001 := sorry
-- </vc-theorems>