-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def box_capacity (length width height : Nat) : Nat := sorry

theorem box_capacity_nonneg (l w h : Nat) :
  box_capacity l w h ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem box_capacity_monotonic_length (l w h : Nat) :
  box_capacity (l + 1) w h ≥ box_capacity l w h := sorry

theorem box_capacity_monotonic_width (l w h : Nat) :
  box_capacity l (w + 1) h ≥ box_capacity l w h := sorry

theorem box_capacity_monotonic_height (l w h : Nat) :
  box_capacity l w (h + 1) ≥ box_capacity l w h := sorry

theorem box_capacity_small_dim (w h : Nat) :
  box_capacity 1 w h = 0 := sorry
-- </vc-theorems>