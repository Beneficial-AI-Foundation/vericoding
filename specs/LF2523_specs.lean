-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def michael_pays (cost : Float) : Float := sorry

theorem michael_pays_is_nonnegative (cost : Float) : 
  michael_pays cost ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem michael_pays_less_than_cost (cost : Float) : 
  michael_pays cost ≤ cost := sorry

-- Note: Removing decimal places theorem since Float doesn't support this directly

theorem michael_pays_full_under_five (cost : Float) :
  cost < 5 → michael_pays cost = cost := sorry

theorem michael_pays_kates_share_capped (cost : Float) :
  let kate_share := min (cost/3) 10
  Float.abs (michael_pays cost - (cost - kate_share)) < 0.0001 := sorry
-- </vc-theorems>