-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_transform_point (sx sy tx ty : Nat) : Bool := sorry 

theorem same_point_always_true {sx sy : Nat} : 
  can_transform_point sx sy sx sy = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem target_less_than_start_always_false {sx sy tx ty : Nat} :
  (tx < sx ∨ ty < sy) → can_transform_point sx sy tx ty = false := sorry

theorem no_valid_moves_if_too_far {sx sy tx ty : Nat} :
  (sx > tx ∧ sy > ty) → can_transform_point sx sy tx ty = false := sorry
-- </vc-theorems>