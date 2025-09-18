-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_real_floor (n : Int) : Int := sorry

theorem negative_and_zero_floors_unchanged
  {floor : Int}
  (h : floor ≤ 0) :
  get_real_floor floor = floor := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem floors_below_13_decreased_by_one
  {floor : Int}
  (h1 : floor > 0)
  (h2 : floor < 13) :
  get_real_floor floor = floor - 1 := sorry

theorem floors_above_12_decreased_by_two
  {floor : Int}
  (h : floor ≥ 13) :
  get_real_floor floor = floor - 2 := sorry

theorem floor_13_maps_to_11 :
  get_real_floor 13 = 11 := sorry
-- </vc-theorems>